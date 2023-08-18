open Narya

(* Poor man's parser, reusing the OCaml parser to make a vaguely usable syntax *)

(* Abstract syntax terms with variable names *)
type pmt =
  | Var : string -> pmt
  | UU : pmt
  | Pi : string * pmt * pmt -> pmt
  | App : pmt * pmt -> pmt
  | Id : pmt * pmt * pmt -> pmt
  | Refl : pmt -> pmt
  | Sym : pmt -> pmt
  | Asc : pmt * pmt -> pmt
  | Lam : string * pmt -> pmt

(* Using a Bwv of variable names, to turn them into De Bruijn indices, we can parse such a term into a synth/checkable one. *)
let rec parse_chk : type n. (string, n) Bwv.t -> pmt -> n Raw.check =
 fun ctx -> function
  | Lam (x, body) -> Lam (parse_chk (Snoc (ctx, x)) body)
  | tm -> Synth (parse_syn ctx tm)

and parse_syn : type n. (string, n) Bwv.t -> pmt -> n Raw.synth =
 fun ctx -> function
  | Var x -> Var (Option.get (Bwv.index x ctx))
  | UU -> UU
  | Pi (x, dom, cod) -> Pi (parse_chk ctx dom, parse_chk (Snoc (ctx, x)) cod)
  | App (fn, arg) -> App (parse_syn ctx fn, parse_chk ctx arg)
  | Id (a, x, y) -> Id (parse_syn ctx a, parse_chk ctx x, parse_chk ctx y)
  | Refl x -> Refl (parse_syn ctx x)
  | Sym x -> Sym (parse_syn ctx x)
  | Asc (tm, ty) -> Asc (parse_chk ctx tm, parse_chk ctx ty)
  | _ -> raise (Failure "Non-synthesizing")

(* Nicer syntax, with a prefix operator for using a variable by name, and infix operators for abstraction, application, and ascription. *)
let ( !! ) x = Var x
let pi x dom cod = Pi (x, dom, cod)
let ( $ ) fn arg = App (fn, arg) (* Left-associative *)
let id a x y = Id (a, x, y)
let refl x = Refl x
let sym x = Sym x
let ( <:> ) tm ty = Asc (tm, ty)
let ( @-> ) x body = Lam (x, body) (* Right-associative *)

(* The current context of assumptions, including names. *)
type ctx = Ctx : 'n Check.ctx * (string, 'n) Bwv.t -> ctx

let ectx = Ctx (Check.empty_ctx, Emp)
let context = ref ectx

(* Functions to synth and check terms *)

let synth (tm : pmt) : Value.value * Value.value =
  let (Ctx (ctx, names)) = !context in
  let raw = parse_syn names tm in
  match Check.synth ctx raw with
  | Some (syn, ty) ->
      let esyn = Check.eval_in_ctx ctx syn in
      (esyn, ty)
  | None -> raise (Failure "Synthesis failure")

let check (tm : pmt) (ty : Value.value) : Value.value =
  let (Ctx (ctx, names)) = !context in
  let raw = parse_chk names tm in
  match Check.check ctx raw ty with
  | Some chk -> Check.eval_in_ctx ctx chk
  | None -> raise (Failure "Checking failure")

(* Assert that a term *doesn't* synthesize or check *)

let unsynth (tm : pmt) : unit =
  let (Ctx (ctx, names)) = !context in
  let raw = parse_syn names tm in
  match Check.synth ctx raw with
  | None -> ()
  | Some _ -> raise (Failure "Synthesis success")

let uncheck (tm : pmt) (ty : Value.value) : unit =
  let (Ctx (ctx, names)) = !context in
  let raw = parse_chk names tm in
  match Check.check ctx raw ty with
  | None -> ()
  | Some _ -> raise (Failure "Checking success")

(* Add to the context of assumptions *)

let assume (x : string) (ty : Value.value) : Value.value =
  let (Ctx (ctx, names)) = !context in
  context := Ctx (Snoc (ctx, ty), Snoc (names, x));
  fst (synth !!x)

(* Check that two terms are, or aren't, equal, at a type or synthesizing *)

let equal_at (tm1 : Value.value) (tm2 : Value.value) (ty : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_some (Equal.equal_at (Check.level_of ctx) tm1 tm2 ty) then ()
  else raise (Failure "Unequal terms")

let unequal_at (tm1 : Value.value) (tm2 : Value.value) (ty : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_none (Equal.equal_at (Check.level_of ctx) tm1 tm2 ty) then ()
  else raise (Failure "Equal terms")

let equal (tm1 : Value.value) (tm2 : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_some (Equal.equal_val (Check.level_of ctx) tm1 tm2) then ()
  else raise (Failure "Unequal terms")

let unequal (tm1 : Value.value) (tm2 : Value.value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Option.is_none (Equal.equal_val (Check.level_of ctx) tm1 tm2) then ()
  else raise (Failure "Equal terms")

(* Infix notation for applying values *)

let ( $$ ) (fn : Value.value) (arg : Value.value) : Value.value =
  Norm.apply fn (Dim.ConstCube.singleton arg)