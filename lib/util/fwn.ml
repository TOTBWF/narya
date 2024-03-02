(* "Forwards" natural numbers.  Backwards natural numbers are the natural lengths of backwards lists, while forwards natural numbers are the natural lengths of forwards lists.  Should not be opened, but used qualified. *)

open Monoid

type zero = private Dummy_zero
type 'n suc = private Dummy_suc

(* We can add a backwards nat to a forwards nat and get a backwards one.  This is the length-level analogue of appending a forward list on the end of a backwards one.  *)

type (_, _, _) bplus =
  | Zero : ('a, zero, 'a) bplus
  | Suc : ('a N.suc, 'b, 'ab) bplus -> ('a, 'b suc, 'ab) bplus

type _ t = Zero : zero t | Suc : 'a t -> 'a suc t

let rec bplus_right : type a b ab. (a, b, ab) bplus -> b t = function
  | Zero -> Zero
  | Suc ab -> Suc (bplus_right ab)

(* We can also get a forwards one as the result.  This is the length-level analogue of prepending a backwards list on the front of a forwards one.  *)

type (_, _, _) fplus =
  | Zero : (N.zero, 'a, 'a) fplus
  | Suc : ('a, 'b suc, 'ab) fplus -> ('a N.suc, 'b, 'ab) fplus

(* Convert a backwards nat to a forwards one. *)

type _ of_bwn = Of_bwn : 'a t * (N.zero, 'a, 'b) bplus -> 'b of_bwn

let of_bwn : type c. c N.t -> c of_bwn =
 fun c ->
  let rec go : type a b c. a N.t -> b t -> (a, b, c) bplus -> c of_bwn =
   fun a b abc ->
    match a with
    | Nat Zero -> Of_bwn (b, abc)
    | Nat (Suc a) -> go (Nat a) (Suc b) (Suc abc) in
  go c Zero Zero

let rec compare : type a b. a t -> b t -> (a, b) Monoid.compare =
 fun a b ->
  match (a, b) with
  | Zero, Zero -> Eq
  | Suc a, Suc b -> (
      match compare a b with
      | Eq -> Eq
      | Neq -> Neq)
  | _ -> Neq

let rec to_int : type a. a t -> int = function
  | Zero -> 0
  | Suc a -> to_int a + 1