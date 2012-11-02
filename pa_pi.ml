open Camlp4.PreCast
module PiGram = MakeGram(Lexer)

type var = string
type const = True | False | Int of int | Channel of string
type expression = Var of var | Bval of const | Op of string * expression * expression
type proc = Zero
	| New of expression * proc
	| Par of proc * proc
	| In of expression * expression list * proc
	| Out of expression * expression list * proc
	| Inrec of expression * expression list * proc
	| Cond of expression * proc * proc
	| Print of expression list

let process = PiGram.Entry.mk "process"

let par_assoc_left = function
	| x :: xs -> List.fold_left (function p1 -> function p2 -> Par (p1, p2)) x xs
	| _ -> failwith "Parse error"

EXTEND PiGram
	GLOBAL: process;

	variable:
		[ [ `LIDENT x -> x ] ];
	constant:
		[ [ "true" -> True
		| "false" -> False
		| `INT (i, _) -> Int i ] ];
	operator:
		[ [ "+" -> "+" | "*" -> "*" | "-" -> "-" | "/" -> "/" | "=" -> "=" | "neq" -> "neq" | ">" -> ">" | "<" -> "<" | "and" -> "and" | "or" -> "or" ] ];
	expression:
		[ [ v = variable -> Var v
		| c = constant -> Bval c
		| "("; e1 = SELF; _op_ = operator; e2 = SELF; ")" -> Op (_op_, e1, e2) ] ];
	def:
		[ [ e = expression; "["; vl = LIST0 variable SEP ","; "]"; "="; p = process -> Inrec (e, List.map (function x -> Var x) vl, p) ] ];
	q_m:
		[ [ "*?" | "?*" ] ];
	iin:
		[ [ "." | "in" ] ];
	iin_p:
		[ [ OPT [ iin; p = process -> p ] ] ];
	process:
		[ [ "stop" -> Zero
		| "("; ")" -> Zero
		| e = expression; "!"; "["; el = LIST0 expression SEP ","; "]"; p = iin_p -> Out (e, el, match p with None -> Zero | Some p -> p)
		| e = expression; "?"; "["; vl = LIST0 variable SEP ","; "]"; p = iin_p -> In (e, List.map (function x -> Var x) vl, match p with None -> Zero | Some p -> p)
		| e = expression; q_m; "["; vl = LIST0 variable SEP ","; "]"; p = iin_p -> Inrec (e, List.map (function x -> Var x) vl, match p with None -> Zero | Some p -> p)
		| "*"; e = expression; "?"; "["; vl = LIST0 variable SEP ","; "]"; p = iin_p -> Inrec (e, List.map (function x -> Var x) vl, match p with None -> Zero | Some p -> p)
		| "new"; e = expression; "in"; p = SELF -> New (e, p)
		| "("; "v"; e = expression; ")"; "("; p = SELF; ")" -> New (e, p)
		| "("; pl = LIST1 SELF SEP "|"; ")" -> par_assoc_left pl
		| "if"; e = expression; "then"; p1 = SELF; "else"; p2 = SELF -> Cond (e, p1, p2)
		| "def"; irl = LIST1 def SEP "and"; "in"; q = SELF -> List.fold_right (function p1 -> function p2 -> New (p1, p2)) (List.map (function Inrec (v, _, _) -> v | _ -> failwith "Parse error") irl) (par_assoc_left (irl @ [q]))
		| "print"; "!"; "["; el = LIST1 expression SEP ","; "]" -> Print el ] ];

END

let parse input = PiGram.parse_string process (Loc.mk "<string>") input
