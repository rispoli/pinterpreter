(*eccezione*)
exception SyntaxError;;

(*sintassi*)
type var = string;;
type const = True | False | Int of int | Channel of string (* <--- same as label, new name with gensym *);;
type expression = Var of var | Bval of const | Op of string * expression * expression;;
type proc = Zero
    | New of expression * proc (* was var * proc *)
    | Par of proc * proc
    | In of expression * expression list * proc
    | Out of expression * expression list * proc
    | Inrec of expression * expression list * proc
    | Cond of expression * proc * proc
    | Print of expression list;;

let p = ref 0;;

let c2s c = Char.escaped c;;

let isletter l = let c = Char.code l in (64 < c & c < 91) || (96 < c & c < 123) || (c = 95);; (* [a-zA-Z_] *)

let isint n = let c = Char.code n in 47 < c & c < 58;; (* [0-9] *)

(*funzione per testare se un token appartiene al linguaggio [se e' una parola riservata]*)
(* (x <> "true") & x <> "false" ... *)
let isname = function
    | x when (List.fold_left (&) true (List.map ((<>) x) ["true"; "false"; "stop"; "new"; "if"; "def"; "print"; "and"; "or"; "neq"; "in"])) -> isletter x.[0]
    | _ -> false;;

(*funzione per estrarre il prossimo token*)
let rec next s = try match s.[!p] with
        ' ' | '\n' | '\t' -> p := !p + 1; next s
        | n when (isint n) -> let acc = ref (c2s n) in
            p := !p + 1;
            while (isint s.[!p]) do
                acc := !acc ^ (c2s s.[!p]);
                p := !p + 1
            done;
            !acc
        | l when (isletter l) -> let acc = ref (c2s l) in
            p := !p + 1;
            while (isletter s.[!p]) || (isint s.[!p]) do
                acc := !acc ^ (c2s s.[!p]);
                p := !p + 1
            done;
            !acc
        | x -> p := !p + 1; (c2s x)
    with Invalid_argument "index out of bounds" -> "Fine";;
(* torna indietro nella stringa di input di lunghezza(s) caratteri perche' non era questa la strada
 * da intraprendere e lo notifica agli altri lanciando un'eccezione *)
let raise_s_e s e =
    (p := !p - (String.length s); raise e);;

(*corpo del parser*)
let parse s =
(*    interpreta il prossimo token come una var*)
    let rec var s =
        let v = next s in
            if isname v then
                v
            else
                raise_s_e v SyntaxError
(*				interpreta il prossimo token come un intero*)
    and integer s =
        let i = next s in
            if isint i.[0] then
                int_of_string i
            else
                raise_s_e i SyntaxError
(*    interpreta il prossimo token come una costante*)
    and const s = try Int (integer s)
            with SyntaxError -> match next s with
                | "true" -> True
                | "false" -> False
                | c -> raise_s_e c SyntaxError
(*    interpreta il prossimo token come un operatore*)
    and op s =
        let o = next s in match o with
            "+" | "-" | "*" | "/" | "and" | "or" | "=" | ">" | "<" | "neq" -> o
            | _ -> raise_s_e o SyntaxError (* necessario tornare indietro se si verifica qualche errore cercando di parsificare una Op che invece era un (x(!/?/*?)[] in ... | ... ) *)
(*    interpreta i prossimi token come una espressione => restituisce Bval/Op*)
    and expr s = try Var (var s)
            with SyntaxError -> try Bval (const s)
                with SyntaxError -> let ns = next s in match ns with
                    | "(" -> let tmp = !p - 1 in (try let e1 = expr s and _op = op s and e2 = expr s in
                                (match next s with
                                    | ")" -> Op (_op, e1, e2)
                                    | _ -> raise SyntaxError)
                        with SyntaxError -> p := tmp; raise SyntaxError)
                    | _ -> raise_s_e ns SyntaxError
(*    interpreta i prossimi token come una lista di variabili*)
    and arg_list_var s =
            if next s = "[" then
                let rec parse_args s acc =
                    try let a = var s in
                                match next s with
                                    | "," -> parse_args s ((Var a) :: acc)
                                    | "]" -> List.rev ((Var a) :: acc)
                                    | _ -> raise SyntaxError
                    with SyntaxError -> if next s = "]" && acc = [] then [] else raise SyntaxError
                        in parse_args s []
            else
                raise SyntaxError
 (*    interpreta i prossimi token come una lista di espressioni*)
    and arg_list_expr s=
        if next s ="[" then
                let rec parse_args s acc =
                    try let a = expr s in
                                match next s with
                                    | "," -> parse_args s (a :: acc)
                                    | "]" -> List.rev (a :: acc)
                                    | _ -> raise SyntaxError
                    with SyntaxError -> if next s = "]" && acc = [] then [] else raise SyntaxError
                        in parse_args s []

        else
            raise SyntaxError
(*    interpreta i prossimi token come una lista di def*)
    and parseDef s acc accv=
(*				    aggiunge le new*)
        let rec addNew pr l =
            match l with
                [] -> pr
              | x::xs -> addNew (New((Var x),pr)) xs
(*        aggiunge gli input ricorsivi*)
        and addInRec l =
            match l with
                x::[] -> x
              | x::xs -> Par(addInRec xs,x)
              | [] -> raise SyntaxError
(*        corpo della parse def*)
        in
        let v=(var s) and l=(arg_list_var s) and i=(next s) and pr=(proc s) in
            if (i="=") then
                let n=(next s) in
                    if(n="and")then
                        parseDef s ((Inrec((Var v),l,pr))::acc) (v::accv)
                    else
                        if(n="in")then
                            addNew (addInRec ((proc s)::(Inrec((Var v),l,pr))::acc)) (v::accv)
                        else
                            raise SyntaxError
            else
                raise SyntaxError
(*    interpreta i prossimi token come un processo*)
    and proc s =
        let v=next s in
           match v with
            | "stop" -> Zero
            | "new" -> let _expr = var s in
                if next s = "in" then
                    New (Var _expr, proc s)
                else
                    raise SyntaxError
(*********************************************************************************************************************)
(* versione ricorsiva di parsePar. *)
(*********************************************************************************************************************)
            | "(" -> let rec parsePar s acc =
                let p1 = (proc s) and c = (next s) in
                    (
                        if (c = "|") then
                            parsePar s (p1 :: acc)
                        else
                           if (c = ")") then
                                if acc = [] then
                                    [p1]
                                else
                                    List.rev (p1 :: acc)
                           else
                              raise SyntaxError
                    ) in
                    let make_par x y = Par (x, y) in
                (match parsePar s [] with
                    | x :: [] -> x
                    | x :: xs -> List.fold_left (make_par) x xs
                    | _ -> raise SyntaxError)
(**********************************************************************************************************************)
(*versione iterativa di parsePar*)
(*********************************************************************************************************************) 
(*            | "(" -> let parsePar s =
                         let p1=(proc s) and c=ref (next s) in
                             (
                                 let acc = ref p1 in
                                 while (!c="|") do
                                     let p2=(proc s) in
                                         (
                                             c:=(next s);
                                             acc := Par(!acc,p2);
                                         )
                                 done;
                                 if (!c=")") then
                                     !acc
                                 else
                                     raise SyntaxError
                             ) in
                             parsePar s
*)
(*********************************************************************************************************************)
            | "def" -> parseDef s [] []
            | "if" -> let _expr = expr s in
                if next s = "then" then
                    let pT = proc s in
                        if next s = "else" then
                            Cond (_expr, pT, proc s)
                        else
                            raise SyntaxError
                else
                    raise SyntaxError
            | "print" -> if next s = "!" then
                            let args = arg_list_expr s in Print args
                        else
                            raise SyntaxError
            | _ -> let sym = next s in
                      (match sym with
                          "!" -> let args = arg_list_expr s in if next s = "in" then Out (Var v, args, proc s) else raise SyntaxError
                        | "?" -> let args = arg_list_var s in if next s = "in" then In (Var v, args, proc s) else raise SyntaxError
                        | "*" -> if next s = "?" then
                                        let args = arg_list_var s in if next s = "in" then Inrec (Var v, args, proc s) else raise SyntaxError
                                 else
                                         raise SyntaxError
                        | _ -> raise_s_e sym SyntaxError)
    in (p := 0; proc (s ^ "#"));;
