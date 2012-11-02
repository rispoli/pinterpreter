type 'a t = { mutable c : 'a list }

exception Empty

let create () = { c = [] }

let fill s l = s.c <- l

let clear s = s.c <- []

let to_list s = s.c

let add_qhead x s = s.c <- x :: s.c

let add_qtail x s = s.c <- s.c @ [x]

let qhead s =
  match s.c with
    hd::tl -> s.c <- tl; hd
  | []     -> raise Empty

let qtail s =
  let rec qtailrec l acc =
    match l with
        [] -> raise Empty
      | tl::[] -> s.c <- List.rev acc; tl
      | x::xs -> qtailrec xs (x::acc)
  in qtailrec s.c []

let is_empty s = (s.c = [])

let length s = List.length s.c

let car s =
  match s.c with
    hd::_ -> hd
  | []     -> raise Empty

let cdr s =
  match s.c with
    _::tl -> { c = tl}
  | [] -> raise Empty

(* parte da spostare in un file (e.g.: map.ml) quando avremo il modulo per la
 * dequeue *)

exception NotFound

let rec lookup k l =
  try
    match car l with
      | (k1, v) when (k1 = k) -> v
      | _ -> lookup k (cdr l)
  with Empty -> raise NotFound

let is_in_map k l =
  try
    let _ = lookup k l in true
  with NotFound -> false

let add_map e l = add_qhead e l

let add_map_u (k, v) l = if is_in_map k l then l else (add_map (k, v) l; l)

let change_map k v l =
  if is_in_map k l then
      (fill l (List.filter ((function x -> function (k, v) -> x <> k) k) (to_list l)); add_map (k, v) l)
  else raise NotFound

(* dati di prova, togliere una volta sviluppati tutti i metodi necessari *)

let l = create();;
add_qhead (7,"c") l;;
add_qhead (6,"b") l;;
add_qhead (5,"a") l;;

(* Coppo says: eval_exp env expr e poi eval_exp su una lista di expr es: c![lista expr]
 * [utilizzare List.combine] *)
