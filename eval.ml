(*eccezione*)
exception Reduce

(*delta_rules*)
let delta = function
	| Op(opr, Bval x, Bval y) when opr = "="
		-> if x=y then True else False
	| Op(opr, Bval x, Bval y) when opr = "neq"
		-> if x<>y then True else False
	| Op(opr, Bval(Int x), Bval(Int y)) when opr = "<"
		-> if x<y then True else False
	| Op(opr, Bval(Int x), Bval(Int y)) when opr = ">"
		-> if x>y then True else False

	| Op(opr, Bval x, Bval y) when opr = "and"
		-> (match (x,y) with
			(True,True) -> True
			| _ -> False)
	| Op(opr,Bval x,Bval y) when opr = "or"
		-> (match (x,y) with
			(False,False) -> False
			| _ -> True)

	| Op(opr, Bval(Int x), Bval(Int y)) when opr = "+"
		-> Int ((+) x y)
	| Op(opr, Bval(Int x), Bval(Int y)) when opr = "-"
		-> Int ((-) x y)
	| Op(opr, Bval(Int x), Bval(Int y)) when opr = "*"
		-> Int (( * ) x y)
	| Op(opr, Bval(Int x), Bval(Int y)) when opr = "/"
		-> Int ((/) x y)

	| _ -> raise Reduce

(*controlla se un'espressione e' completamente valutata*)
let rec evaluated x = match x with
	| Bval _ -> true
	| _ -> false

(*valuta un'espressione in un ambiente per passi*)
let eval_expr e env =
	let rec eval_i = function
		| Op(opr, a1, a2) when not (evaluated a1) ->
			eval_i (Op(opr, eval_i a1, a2))
		| Op(opr, a1, a2) when not (evaluated a2) ->
			eval_i (Op(opr, a1, eval_i a2))
		| Op(opr, a1, a2) ->
			Bval (delta (Op(opr, a1, a2)))
		| Var x -> (try Bval (Env.valinenv (Var x) env) with Env.ArgNotInDom -> failwith ("No binding for variable " ^ x ^ " found."))
		| _ -> raise Reduce
	in match if evaluated e then e else eval_i e with
		| Bval x -> x
		| _ -> raise Reduce
