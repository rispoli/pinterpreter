module type SigCoda =
	sig
		type 'a t
		exception CodaVuota
		val createq: unit -> 'a t
		val isemptyq: 'a t -> bool
		val addhdq: 'a -> 'a t -> unit
		val addtlq: 'a -> 'a t -> unit
		val takehdq: 'a t -> unit
		val qhd: 'a t -> 'a
	end

module Coda : SigCoda =
	struct

		type 'a t = { mutable c : 'a list }

		exception CodaVuota

		let createq () = { c = [] }

		let isemptyq q = (q.c = [])

		let addhdq x q = q.c <- x :: q.c

		let addtlq x q = q.c <- q.c @ [x]

		let takehdq q =
			match q.c with
				  hd::tl -> q.c <- tl
				| []     -> raise CodaVuota

		let qhd q =
			match q.c with
				  hd::tl -> hd
				| []     -> raise CodaVuota

	end
