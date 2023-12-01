open Bwd
open Parser

(* Translate a parse observation into something that shows the names of notations rather than their internal abstract representations, for easier inspection and testing.  Note that since we intercept the parse tree before the "compilation" step, there is no name resolution, so this doesn't need to be run inside a Yuujinchou handler and can use unbound variables. *)

type obs =
  | Flag of Notation.flag
  | Ident of string option
  | Term of parse_tree
  | Constr of string
  | Field of string

and parse_tree =
  | Notn of string * obs list
  | App of parse_tree * parse_tree
  | Ident of string
  | Constr of string
  | Field of string
  | Numeral of Q.t
  | Abs of [ `Normal | `Cube ] * string option list * parse_tree

let rec get_obs (obs : Notation.observation) : obs =
  match obs with
  | Flagged f -> Flag f
  | Ident x -> Ident x
  | Term r -> Term (get_tree r)
  | Constr c -> Constr c
  | Field f -> Field f

and get_tree : type lt ls rt rs. (lt, ls, rt, rs) Notation.parse -> parse_tree =
 fun r ->
  match r with
  | Infix n ->
      Notn
        ( Notation.name n.notn,
          List.map get_obs (Term n.first :: Bwd.to_list (Snoc (n.inner, Notation.Term n.last))) )
  | Prefix n ->
      Notn
        (Notation.name n.notn, List.map get_obs (Bwd.to_list (Snoc (n.inner, Notation.Term n.last))))
  | Postfix n -> Notn (Notation.name n.notn, List.map get_obs (Term n.first :: Bwd.to_list n.inner))
  | Outfix n -> Notn (Notation.name n.notn, List.map get_obs (Bwd.to_list n.inner))
  | App a -> App (get_tree a.fn, get_tree a.arg)
  | Ident x -> Ident x
  | Constr x -> Constr x
  | Field x -> Field x
  | Numeral n -> Numeral n
  | Abs { cube; vars; body; right_ok = _ } -> Abs (cube, vars, get_tree body)

let parse state str =
  let (Wrap tm) = Parse.term state str in
  get_tree tm
