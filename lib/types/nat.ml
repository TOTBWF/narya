open Bwd
open Bwd.Infix
open Util
open Dim
open Core
open Parser
open Notations
open Compile
open Term

let ([ nn; zero; suc; plus; times; ind ] : (Constant.t, N.six) Util.Vec.t) =
  Util.Vec.map Constant.intern [ "N"; "O"; "S"; "plus"; "times"; "N_ind" ]

let ([ zero'; suc' ] : (Constr.t, N.two) Util.Vec.t) = Util.Vec.map Constr.intern [ "0"; "1" ]

let install () =
  Hashtbl.add Global.types nn (UU D.zero);
  Hashtbl.add Global.constants nn
    (Data
       {
         params = N.zero;
         indices = Zero;
         constrs =
           Constr.Map.empty
           |> Constr.Map.add zero' (Global.Constr { args = Emp; indices = Emp })
           |> Constr.Map.add suc' (Global.Constr { args = Ext (Const nn, Emp); indices = Emp });
       });
  Hashtbl.add Global.types zero (Const nn);
  Hashtbl.add Global.constants zero (Defined (Leaf (Constr (zero', D.zero, Emp))));
  Hashtbl.add Global.types suc (pi (Const nn) (Const nn));
  Hashtbl.add Global.constants suc
    (Defined (Lam (Suc Zero, Leaf (Constr (suc', D.zero, Emp <: CubeOf.singleton (Var Top))))));
  Hashtbl.add Global.types plus (pi (Const nn) (pi (Const nn) (Const nn)));
  Hashtbl.add Global.types times (pi (Const nn) (pi (Const nn) (Const nn)));
  Hashtbl.add Global.constants plus
    (Defined
       (Lam
          ( Suc (Suc Zero),
            Branches
              ( Top,
                [
                  Branch (zero', Zero, Leaf (Var (Pop Top)));
                  Branch
                    ( suc',
                      Suc Zero,
                      Leaf
                        (App
                           ( Const suc,
                             CubeOf.singleton
                               (App
                                  ( App (Const plus, CubeOf.singleton (Var (Pop (Pop Top)))),
                                    CubeOf.singleton (Var Top) )) )) );
                ] ) )));
  Hashtbl.add Global.constants times
    (Defined
       (Lam
          ( Suc (Suc Zero),
            Branches
              ( Top,
                [
                  Branch (zero', Zero, Leaf (Const zero));
                  Branch
                    ( suc',
                      Suc Zero,
                      Leaf
                        (App
                           ( App
                               ( Const plus,
                                 CubeOf.singleton
                                   (App
                                      ( App (Const times, CubeOf.singleton (Var (Pop (Pop Top)))),
                                        CubeOf.singleton (Var Top) )) ),
                             CubeOf.singleton (Var (Pop (Pop Top))) )) );
                ] ) )));
  Hashtbl.add Global.types ind
    (pi
       ((* P : *) pi (Const nn) (UU D.zero))
       (pi
          ((* z : *) app (Var Top) (Const zero))
          (pi
             ((* s : *)
              pi ((* n : *) Const nn)
                (pi
                   ((* pn : *)
                    app (Var (Pop (Pop Top))) (Var Top))
                   (app (Var (Pop (Pop (Pop Top)))) (app (Const suc) (Var (Pop Top))))))
             (pi ((* n : *) Const nn) (app (Var (Pop (Pop (Pop Top)))) (Var Top))))));
  Hashtbl.add Global.constants ind
    (Defined
       (Lam
          ( Suc (Suc (Suc (Suc Zero))),
            Branches
              ( Top,
                [
                  Branch (zero', Zero, Leaf (Var (Pop (Pop Top))));
                  Branch
                    ( suc',
                      Suc Zero,
                      Leaf
                        (app
                           (app (Var (Pop (Pop Top))) (Var Top))
                           (app
                              (app
                                 (app
                                    (app (Const ind) (Var (Pop (Pop (Pop (Pop Top))))))
                                    (Var (Pop (Pop (Pop Top)))))
                                 (Var (Pop (Pop Top))))
                              (Var Top))) );
                ] ) )))

open Monad.Ops (Monad.Maybe)

let plusn =
  make ~name:"+" ~tightness:0. ~left:Open ~right:Open ~assoc:Left ~tree:(fun n ->
      eop (Op "+") (Done n))

let () =
  add_compiler plusn
    {
      compile =
        (fun ctx obs ->
          let x, obs = get_term obs in
          let y, obs = get_term obs in
          let () = get_done obs in
          let* x = compile ctx x in
          let* y = compile ctx y in
          return (Raw.Synth (App (App (Const plus, x), y))));
    }

let timesn =
  make ~name:"*" ~tightness:1. ~left:Open ~right:Open ~assoc:Left ~tree:(fun n ->
      eop (Op "*") (Done n))

let () =
  add_compiler timesn
    {
      compile =
        (fun ctx obs ->
          let x, obs = get_term obs in
          let y, obs = get_term obs in
          let () = get_done obs in
          let* x = compile ctx x in
          let* y = compile ctx y in
          return (Raw.Synth (App (App (Const times, x), y))));
    }

let () = Builtins.builtins := !Builtins.builtins |> State.add plusn |> State.add timesn
