module type SigHeap =
	functor (E: SigEnv)  ->
		sig
			exception HeapException
			type ('a,'b) t
			val createh: unit -> ('a,'b) t
			val addh: 'a -> ?v:'b Coda.t -> ('a,'b) t -> unit
			val isindomh: 'a -> ('a,'b) t -> bool
			val valinh: 'a -> ('a,'b) t -> 'b Coda.t
			val update: 'a -> 'b Coda.t -> ('a, 'b) t -> unit
			val remove: 'a -> ('a,'b) t -> unit
		end

module Heap : SigHeap =
	functor (E: SigEnv)  ->
		struct

			exception HeapException

			type ('a,'b) t = ('a, ('b Coda.t)) E.t ref

			let createh () = ref E.emptyenv

			let addh x ?(v = Coda.createq ()) h = h := E.addenv (x, v) !h

			let valinh k h =
				try
					E.valinenv k !h
				with E.ArgNotInDom -> raise HeapException

			let isindomh k h =
				try
					let _ = valinh k h in true
				with HeapException -> false

			let remove k h =
				try
					h := (E.remove k !h)
				with E.ArgNotInDom -> raise HeapException

			let update k v1 h =
				if isindomh k h then
					(remove k h; addh k ~v:v1 h)
				else raise HeapException

		end


		(* Per istanziare il modulo: module ModuleName = Heap(Env) *)
