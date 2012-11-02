(*creo una istanza di module che costruisce un heap usando come funtore un env*)
module Heap_E = Heap(Env)

(*importo i moduli*)
open Coda
open Env
open Heap_E

(*classe della macchina astratta*)
class mk_ab_mac p =
(*	let ini = createq () in*)
		object (self)
			val heap = createh ()
			val run = (*ini*) createq ()
			val c_count = ref 0
			val _in = "." (* " in " *)

(*   genera nomi univoci per i canali*)
			method private gensym = function () -> incr c_count; "#" ^ string_of_int !c_count

(*   costruisco la lista dei valori delle variabili e delle espressioni in xv rispetto ad env*)
			method private list_in_env xv env =
				let rec lie xv acc = match xv with
						| [] -> List.rev acc
						| Var x :: xs -> lie xs ((valinenv (Var x) env) :: acc)
						| x :: xs -> lie xs ((eval_expr x env) :: acc)
				in lie xv []

(*   aggiunge in env_to_update la lista dei binding delle variabili in var_to_bind con i rispettivi valori*)
			method private update_env expr_to_eval env_of_eval var_to_bind env_to_update =
			 let vv = self#list_in_env expr_to_eval env_of_eval in
				addenvlist (List.combine var_to_bind vv) env_to_update

(*   cerco se un canale e' nell'heap, altrimenti lo aggiungo. ritorno il suo "valore"*)
			method private fetch_or_new c e =
			 let _c =
				try match valinenv (Var c) e with
					| Channel x -> x
					| _ -> failwith "Bad binding"
				with ArgNotInDom -> c
				in
				try (valinh (Channel _c) heap, _c)
					with HeapException -> addh (Channel _c) heap; self#fetch_or_new _c e

(*   prova a prendere il prossimo processo, in caso di errore restituisce zero*)
			method private qhd_safe q = try qhd q with CodaVuota -> (emptyenv, Zero)

			method private const_to_string = function
				| True -> "true"
				| False -> "false"
				| Int x -> string_of_int x
				| Channel c -> c

(*   valuta un'espressione in env, se v=true => valore, se v=false => nome{=valore}*)
			method private eval_expr_env ?(v = false) env = function
				| Var x -> let m = (try (self#const_to_string (valinenv (Var x) env)) with ArgNotInDom -> "") in if v then m else x ^ (if m <> "" then "{=" ^ m ^ "}" else m)
				| Bval x -> self#const_to_string x
				| Op (op, x, y) -> let m = (try (self#const_to_string (eval_expr (Op (op, x, y)) env)) with Failure _ -> "") in if v then m else "( " ^ (self#eval_expr_env env x) ^ " " ^ op ^ " " ^ (self#eval_expr_env env y) ^ " )" ^ (if m<>"" then "{=" ^ m ^ "}" else m)

(*   rimuove una lista di variabili da un ambiente*)
			method private purge_env env xv =
			 List.fold_left (function e' -> function key -> try Env.remove key e' with ArgNotInDom -> e') env xv

(*   converte dalla sinstassi astratta a quella concreata [. al posto di in]*)
			method private concrete = function
				| (_, Zero) -> "stop"
				| (e, Par(p, q)) -> "( " ^ self#concrete (e, p) ^ " | " ^ self#concrete (e, q) ^ " )"
				| (e, New(Var c, p)) -> "( v " ^ c ^ " )( " ^ self#concrete (e, p) ^ " )"
				| (e, Cond(b, p, q)) -> "if " ^ self#eval_expr_env e b ^ " then " ^ self#concrete (e, p) ^ " else " ^ self#concrete (e, q)
				| (e, In(Var c, xv, p)) -> let e' = self#purge_env e xv in (self#eval_expr_env e (Var c)) ^ "?[" ^ (String.concat ", " (List.map (self#eval_expr_env e') xv)) ^ "]" ^ (if p <> Zero then _in ^ self#concrete (e', p) else "")
				| (e, Out(Var c, ev, p)) -> (self#eval_expr_env e (Var c)) ^ "![" ^ (String.concat ", " (List.map (self#eval_expr_env e) ev)) ^ "]" ^ (if p <> Zero then _in ^ self#concrete (e, p) else "")
				| (e, Inrec(Var c, xv, p)) -> let e' = self#purge_env e xv in (self#eval_expr_env e (Var c)) ^ "*?[" ^ (String.concat ", " (List.map (self#eval_expr_env e') xv)) ^ "]" ^ (if p <> Zero then _in ^ self#concrete (e', p) else "")
				| (e, Print ev) -> "print![" ^ (String.concat ", " (List.map (self#eval_expr_env e) ev)) ^ "]"
				| _ -> failwith "Process not correct"

(*   trasforma expr in stringhe senza valutazione*)
			method private _export_expr = function
				| Var x -> x
				| Bval x -> self#const_to_string x
				| Op (op, x, y) -> "(" ^ self#_export_expr x ^ " " ^ op ^ " " ^ self#_export_expr y ^ ")"

(*   funzione per esportare in "formato PROLOG"*)
			method private _export = function
				| (_, Zero) -> "stop"
				| (e, Par(p, q)) -> "par(" ^ self#_export (e, p) ^ ", " ^ self#_export (e, q) ^ ")"
				| (e, New(Var c, p)) -> "nu(" ^ c ^ ", " ^ self#_export (e, p) ^ ")"
				| (e, Cond(b, p, q)) -> "ite(" ^ self#_export_expr b ^ ", " ^ self#_export (e, p) ^ ", " ^ self#_export (e, q) ^ ")"
				| (e, In(Var c, xv, p)) -> "input(" ^ c ^ ", [" ^ (String.concat ", " (List.map (self#_export_expr) xv)) ^ "], " ^ self#_export (e, p) ^ ")"
				| (e, Out(Var c, ev, p)) -> "output(" ^ c ^ ", [" ^ (String.concat ", " (List.map (self#_export_expr) ev)) ^ "], " ^ self#_export (e, p) ^ ")"
				| (e, Inrec(Var c, xv, p)) -> "rec(" ^ c ^ ", [" ^ (String.concat ", " (List.map (self#_export_expr) xv)) ^ "], " ^ self#_export (e, p) ^ ")"
				| (_, Print ev) -> "output(print, [" ^ (String.concat ", " (List.map (self#_export_expr) ev)) ^ "], stop)"
				| _ -> failwith "Process not correct"

(*   metodo pubblico che richiama export passando la testa della coda dei processi running*)
			method export = self#_export (qhd run)

(*   metodo privato che richiama concrete passando la testa della coda dei processi running*)
			method private concrete_run_hd = self#concrete (qhd run)

(*   metodo per vedere ogni passo della riduzione*)
			method steps = try print_endline (self#concrete (qhd run)); self#next; self#steps with CodaVuota -> print_endline "The End"

(*   metodo per vedere solo il risultato della riduzione*)
			method results = try self#next; self#results with CodaVuota -> print_endline "The End"

(*   metodo che compie un passo di riduzione*)
			method private next = match qhd run with
				| (_, Zero) -> takehdq run
				| (e, Par(p, q)) -> takehdq run; addhdq (e, p) run; addtlq (e, q) run
				| (e, New(c, p)) -> takehdq run; let c' = Channel (self#gensym ()) in addh c' heap; addhdq (addenv (c, c') e, p) run
				| (e, Cond(b, p, q)) -> takehdq run;
					let cond = match b with
						| Var x -> valinenv b e
						| _ -> eval_expr b e in
					if cond = True || (cond <> False && cond <> Int 0) then addhdq (e, p) run else addhdq (e, q) run
				| (e, In(Var c, xv, p)) -> let (h_c, _c) = self#fetch_or_new c e in
					(match self#qhd_safe h_c with
						| (e', Out(Var c, ev, q)) -> takehdq run; takehdq h_c; update (Channel _c) h_c heap; addhdq (self#update_env ev e' xv e, p) run; addtlq (e', q) run
						| _ -> takehdq run; addtlq (e, In(Var c, xv, p)) h_c; update (Channel _c) h_c heap)
				| (e, Out(Var c, ev, p)) -> let (h_c, _c) = self#fetch_or_new c e in
					(match self#qhd_safe h_c with
						| (e', In(Var c, xv, q)) -> takehdq run; takehdq h_c; update (Channel _c) h_c heap; addhdq (e, p) run; addtlq (self#update_env ev e xv e', q) run
						| (e', Inrec(Var c, xv, q)) -> takehdq h_c; addtlq (e', Inrec(Var c, xv, q)) h_c; update (Channel _c) h_c heap; takehdq run; addhdq (e, p) run; addtlq (self#update_env ev e xv e', q) run
						| _ -> takehdq run; addtlq (e, Out(Var c, ev, p)) h_c; update (Channel _c) h_c heap)
				| (e, Inrec(Var c, xv, p)) -> let (h_c, _c) = self#fetch_or_new c e in
					(match self#qhd_safe h_c with
						| (e', Out(Var c, ev, q)) -> takehdq h_c; update (Channel _c) h_c heap; addtlq (self#update_env ev e' xv e, p) run; addtlq (e', q) run
						| _ -> takehdq run; addtlq (e, Inrec(Var c, xv, p)) h_c; update (Channel _c) h_c heap)
				| (e, Print ev) -> takehdq run; print_endline (String.concat ", " (List.map (self#eval_expr_env ~v:true e) ev))
				| _ -> failwith "Could not reduce"

			(* utili per il debug, da eliminare alla fine *)
			method g_heap = heap
			method g_run = run
			(* /utili per il debug, da eliminare alla fine *)

			initializer addtlq (emptyenv, p) run
		end
