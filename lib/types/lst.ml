open Bwd
open Bwd.Infix
open Dim
open Core
open Term

let nil = Constr.intern "nil"
let cons = Constr.intern "cons"

let install () =
  let list = Scope.define "List" in
  let ind = Scope.define "List_ind" in
  Hashtbl.add Global.types list (pi (UU D.zero) (UU D.zero));
  Hashtbl.add Global.constants list
    (Data
       {
         params = Suc Zero;
         indices = Zero;
         constrs =
           Constr.Map.empty
           |> Constr.Map.add nil (Global.Constr { args = Emp; indices = Emp })
           |> Constr.Map.add cons
                (Global.Constr
                   {
                     args =
                       Ext
                         ( Var (Top (id_sface D.zero)),
                           Ext (app (Const list) (Term.Var (Pop (Top (id_sface D.zero)))), Emp) );
                     indices = Emp;
                   });
       });
  Hashtbl.add Global.types ind
    (pi (UU D.zero)
       (pi
          (pi (app (Const list) (Var (Top (id_sface D.zero)))) (UU D.zero))
          (pi
             (app (Var (Top (id_sface D.zero))) (constr nil Emp))
             (pi
                (pi
                   (Var (Pop (Pop (Top (id_sface D.zero)))))
                   (pi
                      (app (Const list) (Var (Pop (Pop (Pop (Top (id_sface D.zero)))))))
                      (pi
                         (app
                            (Var (Pop (Pop (Pop (Top (id_sface D.zero))))))
                            (Var (Top (id_sface D.zero))))
                         (app
                            (Var (Pop (Pop (Pop (Pop (Top (id_sface D.zero)))))))
                            (constr cons
                               (Emp
                               <: Var (Pop (Pop (Top (id_sface D.zero))))
                               <: Var (Pop (Top (id_sface D.zero)))))))))
                (pi
                   (app (Const list) (Var (Pop (Pop (Pop (Top (id_sface D.zero)))))))
                   (app
                      (Var (Pop (Pop (Pop (Top (id_sface D.zero))))))
                      (Var (Top (id_sface D.zero)))))))));
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
                                                                       (Pop (Top (id_sface D.zero))))))
                                                          ) );
                                                      ( cons,
                                                        Branch
                                                          ( Suc (Suc Zero),
                                                            ref
                                                              (Case.Leaf
                                                                 (apps
                                                                    (Var
                                                                       (Pop
                                                                          (Pop
                                                                             (Pop
                                                                                (Top
                                                                                   (id_sface D.zero))))))
                                                                    [
                                                                      Var
                                                                        (Pop (Top (id_sface D.zero)));
                                                                      Var (Top (id_sface D.zero));
                                                                      apps (Const ind)
                                                                        [
                                                                          Var
                                                                            (Pop
                                                                               (Pop
                                                                                  (Pop
                                                                                     (Pop
                                                                                        (Pop
                                                                                           (Pop
                                                                                              (Top
                                                                                                 (id_sface
                                                                                                    D
                                                                                                    .zero))))))));
                                                                          Var
                                                                            (Pop
                                                                               (Pop
                                                                                  (Pop
                                                                                     (Pop
                                                                                        (Pop
                                                                                           (Top
                                                                                              (id_sface
                                                                                                 D
                                                                                                 .zero)))))));
                                                                          Var
                                                                            (Pop
                                                                               (Pop
                                                                                  (Pop
                                                                                     (Pop
                                                                                        (Top
                                                                                           (id_sface
                                                                                              D.zero))))));
                                                                          Var
                                                                            (Pop
                                                                               (Pop
                                                                                  (Pop
                                                                                     (Top
                                                                                        (id_sface
                                                                                           D.zero)))));
                                                                          Var
                                                                            (Top (id_sface D.zero));
                                                                        ];
                                                                    ])) ) );
                                                    ] )) )) )) )) )) ))))
