open Bwd
open Bwd.Infix
open Dim
open Core
open Term
open Nat

let nil = Constr.intern "nil"
let cons = Constr.intern "cons"

let install () =
  Nat.install ();
  let vec = Scope.define "Vec" in
  let concat = Scope.define "concat" in
  let ind = Scope.define "Vec_ind" in
  Hashtbl.add Global.types vec (pi (UU D.zero) (pi (Const nn) (UU D.zero)));
  Hashtbl.add Global.constants vec
    (Data
       {
         params = Suc Zero;
         indices = Suc Zero;
         constrs =
           Constr.Map.empty
           |> Constr.Map.add nil
                (Global.Constr { args = Emp; indices = Snoc (Emp, Constr (zero', D.zero, Emp)) })
           |> Constr.Map.add cons
                (Global.Constr
                   {
                     args =
                       Ext
                         ( Const nn,
                           Ext
                             ( Var (Pop (Top (id_sface D.zero))),
                               Ext
                                 ( App
                                     ( App
                                         ( Const vec,
                                           CubeOf.singleton
                                             (Term.Var (Pop (Pop (Top (id_sface D.zero))))) ),
                                       CubeOf.singleton (Term.Var (Pop (Top (id_sface D.zero)))) ),
                                   Emp ) ) );
                     indices =
                       Snoc
                         ( Emp,
                           Constr
                             ( suc',
                               D.zero,
                               Emp
                               <: CubeOf.singleton (Term.Var (Pop (Pop (Top (id_sface D.zero))))) )
                         );
                   });
       });
  Hashtbl.add Global.types concat
    (pi (UU D.zero)
       (pi (Const nn)
          (pi (Const nn)
             (pi
                (apps (Const vec)
                   [ Var (Pop (Pop (Top (id_sface D.zero)))); Var (Pop (Top (id_sface D.zero))) ])
                (pi
                   (apps (Const vec)
                      [
                        Var (Pop (Pop (Pop (Top (id_sface D.zero)))));
                        Var (Pop (Top (id_sface D.zero)));
                      ])
                   (apps (Const vec)
                      [
                        Var (Pop (Pop (Pop (Pop (Top (id_sface D.zero))))));
                        apps (Const plus)
                          [
                            Var (Pop (Pop (Pop (Top (id_sface D.zero)))));
                            Var (Pop (Pop (Top (id_sface D.zero))));
                          ];
                      ]))))));
  Hashtbl.add Global.types ind
    (pi (UU D.zero)
       (pi
          (pi (Const nn)
             (pi
                (apps (Const vec)
                   [ Var (Pop (Top (id_sface D.zero))); Var (Top (id_sface D.zero)) ])
                (UU D.zero)))
          (pi
             (apps (Var (Top (id_sface D.zero))) [ constr zero' Emp; constr nil Emp ])
             (pi
                (pi (Const nn)
                   (pi
                      (Var (Pop (Pop (Pop (Top (id_sface D.zero))))))
                      (pi
                         (apps (Const vec)
                            [
                              Var (Pop (Pop (Pop (Pop (Top (id_sface D.zero))))));
                              Var (Pop (Top (id_sface D.zero)));
                            ])
                         (pi
                            (apps
                               (Var (Pop (Pop (Pop (Pop (Top (id_sface D.zero)))))))
                               [
                                 Var (Pop (Pop (Top (id_sface D.zero))));
                                 Var (Top (id_sface D.zero));
                               ])
                            (apps
                               (Var (Pop (Pop (Pop (Pop (Pop (Top (id_sface D.zero))))))))
                               [
                                 constr suc' (Emp <: Var (Pop (Pop (Pop (Top (id_sface D.zero))))));
                                 constr cons
                                   (Emp
                                   <: Var (Pop (Pop (Pop (Top (id_sface D.zero)))))
                                   <: Var (Pop (Pop (Top (id_sface D.zero))))
                                   <: Var (Pop (Top (id_sface D.zero))));
                               ])))))
                (pi (Const nn)
                   (pi
                      (apps (Const vec)
                         [
                           Var (Pop (Pop (Pop (Pop (Top (id_sface D.zero))))));
                           Var (Top (id_sface D.zero));
                         ])
                      (apps
                         (Var (Pop (Pop (Pop (Pop (Top (id_sface D.zero)))))))
                         [ Var (Pop (Top (id_sface D.zero))); Var (Top (id_sface D.zero)) ])))))));
  Hashtbl.add Global.constants ind
    (Defined
       (ref
          (Case.Lam
             ( D.zero,
               ref
                 (Case.Lam
                    ( D.zero,
                      ref
                        (Case.Lam
                           ( D.zero,
                             ref
                               (Case.Lam
                                  ( D.zero,
                                    ref
                                      (Case.Lam
                                         ( D.zero,
                                           ref
                                             (Case.Lam
                                                ( D.zero,
                                                  ref
                                                    (Case.Branches
                                                       ( Top (id_sface D.zero),
                                                         D.zero,
                                                         Constr.Map.of_list
                                                           [
                                                             ( nil,
                                                               Case.Branch
                                                                 ( Zero,
                                                                   ref
                                                                     (Case.Leaf
                                                                        (Var
                                                                           (Pop
                                                                              (Pop
                                                                                 (Pop
                                                                                    (Top
                                                                                       (id_sface
                                                                                          D.zero)))))))
                                                                 ) );
                                                             ( cons,
                                                               Branch
                                                                 ( Suc (Suc (Suc Zero)),
                                                                   ref
                                                                     (Case.Leaf
                                                                        (apps
                                                                           (Var
                                                                              (Pop
                                                                                 (Pop
                                                                                    (Pop
                                                                                       (Pop
                                                                                          (Pop
                                                                                             (Top
                                                                                                (id_sface
                                                                                                   D
                                                                                                   .zero))))))))
                                                                           [
                                                                             Var
                                                                               (Pop
                                                                                  (Pop
                                                                                     (Top
                                                                                        (id_sface
                                                                                           D.zero))));
                                                                             Var
                                                                               (Pop
                                                                                  (Top
                                                                                     (id_sface
                                                                                        D.zero)));
                                                                             Var
                                                                               (Top
                                                                                  (id_sface D.zero));
                                                                             apps (Const ind)
                                                                               [
                                                                                 Var
                                                                                   (Pop
                                                                                      (Pop
                                                                                         (Pop
                                                                                            (Pop
                                                                                               (Pop
                                                                                                  (Pop
                                                                                                    (
                                                                                                    Pop
                                                                                                    (
                                                                                                    Pop
                                                                                                    (
                                                                                                    Top
                                                                                                    (
                                                                                                    id_sface
                                                                                                    D
                                                                                                    .zero))))))))));
                                                                                 Var
                                                                                   (Pop
                                                                                      (Pop
                                                                                         (Pop
                                                                                            (Pop
                                                                                               (Pop
                                                                                                  (Pop
                                                                                                    (
                                                                                                    Pop
                                                                                                    (
                                                                                                    Top
                                                                                                    (
                                                                                                    id_sface
                                                                                                    D
                                                                                                    .zero)))))))));
                                                                                 Var
                                                                                   (Pop
                                                                                      (Pop
                                                                                         (Pop
                                                                                            (Pop
                                                                                               (Pop
                                                                                                  (Pop
                                                                                                    (
                                                                                                    Top
                                                                                                    (
                                                                                                    id_sface
                                                                                                    D
                                                                                                    .zero))))))));
                                                                                 Var
                                                                                   (Pop
                                                                                      (Pop
                                                                                         (Pop
                                                                                            (Pop
                                                                                               (Pop
                                                                                                  (Top
                                                                                                    (
                                                                                                    id_sface
                                                                                                    D
                                                                                                    .zero)))))));
                                                                                 Var
                                                                                   (Pop
                                                                                      (Pop
                                                                                         (Top
                                                                                            (id_sface
                                                                                               D
                                                                                               .zero))));
                                                                                 Var
                                                                                   (Top
                                                                                      (id_sface
                                                                                         D.zero));
                                                                               ];
                                                                           ])) ) );
                                                           ] )) )) )) )) )) )) ))))
