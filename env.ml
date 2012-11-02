module type SigEnv =
	sig
		type ('a,'b) t
		exception ArgNotInDom
		val emptyenv: ('a,'b) t
		val isemptyenv: ('a,'b) t -> bool
		val addenv: 'a * 'b -> ('a,'b) t -> ('a,'b) t
		val addenvlist: ('a * 'b) list -> ('a,'b) t -> ('a,'b) t
		val isindom: 'a -> ('a,'b) t -> bool
		val valinenv: 'a -> ('a,'b) t -> 'b
		val remove: 'a -> ('a, 'b) t -> ('a, 'b) t
	end

module Env : SigEnv =
	struct

		type ('a,'b) t = ('a * 'b) list

		exception ArgNotInDom

		let emptyenv = []

		let isemptyenv e = ( e = [] )

		let addenv x e = ( x::e )

		let rec addenvlist l e = match List.rev l with
			  [] -> e
			| x :: xs -> addenvlist xs (addenv x e)

		let rec valinenv n e = match e with
			  [] -> raise ArgNotInDom
			| (k, v) :: xs when (k = n) -> v
			| _ :: xs -> valinenv n xs

		let isindom n e =
			try
				let _ = valinenv n e in true
			with ArgNotInDom -> false

		let remove k e =
			if isindom k e then
				List.filter ((function k -> function (x, _) -> k <> x) k) e
			else raise ArgNotInDom

	end
