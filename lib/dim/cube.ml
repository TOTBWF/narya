open Bwd
open Util
open Tlist
open Hlist
open Sface
open Bwsface

(* A cube of dimension 'm is a data structure that records one object for each strict face of 'm, in a ternary tree so that they can be accessed randomly by strict face as well as sequentially.  We allow the *type* of each object to depend on the *domain* of the strict face that indexes it, by parametrizing the notion with a functor.  We also allow an extra dependence on some additional type, so that an individual functor application can be parametric. *)

module type Fam = sig
  (* 'a is the domain of the strict face, 'b is an extra parameter. *)
  type ('a, 'b) t
end

module Cube (F : Fam) = struct
  (* First we define an auxiliary data structure.  An ('m, 'n, 'b) gt is a ternary tree of height 'm whose interior nodes have their last branch special, and whose leaves are labeled by an element of F(n-k,b) , where k is the number of non-special branches taken to lead to the leaf.  Thus there is exactly one element of type F(n,b), 2*m elements of type F(n-1,b), down to 2^m elements of type F(n-m,b).  *)
  type (_, _, _) gt =
    | Leaf : ('n, 'b) F.t -> (D.zero, 'n, 'b) gt
    | Branch :
        (('m, 'n, 'b) gt, Endpoints.len) Bwv.t * ('m, 'n D.suc, 'b) gt
        -> ('m D.suc, 'n D.suc, 'b) gt

  (* Now a cube of dimension 'n with parameter 'b is obtained by coinciding the labeling dimension and the height. *)
  type ('n, 'b) t = ('n, 'n, 'b) gt

  (* This two-step data definition means that all the functions that act on them must also be defined in terms of a gt version.  However, in the interface we expose only the t versions. *)

  (* For instance, we can compute the dimension of a cube. *)
  let rec gdim : type m n b. (m, n, b) gt -> m D.t = function
    | Leaf _ -> D.zero
    | Branch (_, br) -> D.suc (gdim br)

  let dim : type n b. (n, b) t -> n D.t = fun tr -> gdim tr

  (* A cube of dimension zero is just an element. *)

  let singleton : type b. (D.zero, b) F.t -> (D.zero, b) t = fun x -> Leaf x

  (* A strict face is an index into a face tree.  *)

  let rec gfind :
      type m n k km nm b.
      (km, nm, b) gt -> (k, m, km) D.plus -> (n, m, nm) D.plus -> (k, km) sface -> (n, b) F.t =
   fun tr km nm d ->
    match (tr, d) with
    | Leaf x, Zero ->
        let Zero = km in
        let Zero = nm in
        x
    | Branch (br, _), End (d, e) ->
        let (Le km') = plus_of_sface d in
        let Eq = D.minus_uniq' (dom_sface d) (Suc km') km in
        let (Suc nm') = nm in
        gfind (Bwv.nth e br) km' nm' d
    | Branch (_, br), Mid d ->
        let (Suc km) = N.plus_suc km in
        gfind br km nm d

  let find : type n k b. (n, b) t -> (k, n) sface -> (k, b) F.t =
   fun tr d ->
    let (Le km) = plus_of_sface d in
    gfind tr km km d

  let rec gfind_top : type k n b. (k, n, b) gt -> (n, b) F.t = function
    | Leaf x -> x
    | Branch (_, br) -> gfind_top br

  let find_top : type n b. (n, b) t -> (n, b) F.t = fun tr -> gfind_top tr

  (* Heterogeneous lists and multimaps, which take the current face as input everywhere in addition to the values in the data structure.  We use the technique of heteregeneous generic traversal, which is a much more significant win here in terms of coding because we only have to descend into gt's once, and all the other operations can be derived from the simpler t version. *)

  module Heter = struct
    (* An hlist of elements of F.t, with the first parameter fixed but the second varying along the list. *)
    type (_, _) hft =
      | [] : ('n, nil) hft
      | ( :: ) : ('n, 'x) F.t * ('n, 'xs) hft -> ('n, ('x, 'xs) cons) hft

    (* An hlist of gt's, with the first two parameters (dimensions) fixed but the third varying along the list.  *)
    type (_, _, _) hgt =
      | [] : ('m, 'n, nil) hgt
      | ( :: ) : ('m, 'n, 'x) gt * ('m, 'n, 'xs) hgt -> ('m, 'n, ('x, 'xs) cons) hgt

    (* A relational function constructing, for any tlist of value types, the corresponding tlist of gt types.  *)
    type (_, _, _, _) hgts =
      | Nil : ('m, 'n, nil, nil) hgts
      | Cons : ('m, 'n, 'xs, 'ys) hgts -> ('m, 'n, ('x, 'xs) cons, (('m, 'n, 'x) gt, 'ys) cons) hgts

    (* The next two functions are inverse isomorphisms. *)
    let rec hlist_of_hgt : type m n xs ys. (m, n, xs, ys) hgts -> (m, n, xs) hgt -> ys hlist =
     fun hs xs ->
      match (hs, xs) with
      | Nil, [] -> []
      | Cons hs, x :: xs -> x :: hlist_of_hgt hs xs

    let rec hgt_of_hlist : type m n xs ys. (m, n, xs, ys) hgts -> ys hlist -> (m, n, xs) hgt =
     fun hs xs ->
      match (hs, xs) with
      | Nil, [] -> []
      | Cons hs, x :: xs -> x :: hgt_of_hlist hs xs

    (* hgts preserves validity of tlists. *)
    let rec tlist_hgts : type m n xs ys. (m, n, xs, ys) hgts -> xs Tlist.t -> ys Tlist.t =
     fun hs xs ->
      match (hs, xs) with
      | Nil, Nil -> Nil
      | Cons hs, Cons xs -> Cons (tlist_hgts hs xs)

    (* And any tlist of value types has some corresponding list of gts. *)
    type (_, _, _) has_hgts = Hgts : ('m, 'n, 'xs, 'xss) hgts -> ('m, 'n, 'xs) has_hgts

    let rec hgts_of_tlist : type m n xs. xs Tlist.t -> (m, n, xs) has_hgts = function
      | Nil -> Hgts Nil
      | Cons xs ->
          let (Hgts xss) = hgts_of_tlist xs in
          Hgts (Cons xss)

    (* Extract the pieces of an hlist of gt's. *)
    let rec lab : type n bs. (D.zero, n, bs) hgt -> (n, bs) hft = function
      | [] -> []
      | Leaf x :: xs -> x :: lab xs

    type (_, _, _) ends =
      | Ends : ('m, 'n, 'bs, 'hs) hgts * ('hs, Endpoints.len) Bwv.Heter.ht -> ('m, 'n, 'bs) ends

    let rec ends : type m n bs. (m D.suc, n D.suc, bs) hgt -> (m, n, bs) ends =
     fun xss ->
      match xss with
      | [] -> Ends (Nil, [])
      | Branch (es, _) :: xs ->
          let (Ends (hs, ess)) = ends xs in
          Ends (Cons hs, es :: ess)

    let rec mid : type m n bs. (m D.suc, n D.suc, bs) hgt -> (m, n D.suc, bs) hgt = function
      | [] -> []
      | Branch (_, m) :: xs -> m :: mid xs

    (* Construct an hlist of gt's as leaves or branches.  *)
    let rec leaf : type n bs. (n, bs) hft -> (D.zero, n, bs) hgt = function
      | [] -> []
      | x :: xs -> Leaf x :: leaf xs

    let rec branch :
        type m n bs hs.
        (m, n, bs, hs) hgts ->
        (hs, Endpoints.len) Bwv.Heter.ht ->
        (m, n D.suc, bs) hgt ->
        (m D.suc, n D.suc, bs) hgt =
     fun hs endss mids ->
      match (hs, endss, mids) with
      | Nil, [], [] -> []
      | Cons hs, ends :: endss, mid :: mids -> Branch (ends, mid) :: branch hs endss mids
  end

  (* OCaml can't always tell from context what [x ; xs] should be; in particular it often fails to notice hfts.  So we also give a different syntax that is unambiguous.  *)
  module Infix = struct
    let hnil : type n. (n, nil) Heter.hft = []

    let ( @: ) : type n x xs. (n, x) F.t -> (n, xs) Heter.hft -> (n, (x, xs) cons) Heter.hft =
     fun x xs -> x :: xs
  end

  open Infix

  module Monadic (M : Monad.Plain) = struct
    open Monad.Ops (M)
    module BwvM = Bwv.Monadic (M)

    (* The function that we apply on a generic traversal must be polymorphic over the domain dimension of the face, so we wrap it in a record. *)
    type ('n, 'bs, 'cs) pmapperM = {
      map : 'm. ('m, 'n) sface -> ('m, 'bs) Heter.hft -> ('m, 'cs) Heter.hft M.t;
    }

    (* Finally, here is the generic monadic traversal of a gt. *)
    let rec gpmapM :
        type k m km n b bs cs l.
        (k, m, km) D.plus ->
        (l, m, n) D.plus ->
        (k, l) bwsface ->
        (n, (b, bs) cons, cs) pmapperM ->
        (m, km, (b, bs) cons) Heter.hgt ->
        cs Tlist.t ->
        (m, km, cs) Heter.hgt M.t =
     fun km lm d g trs cst ->
      match trs with
      | Leaf _ :: _ ->
          let Zero, Zero = (km, lm) in
          let* x = g.map (sface_of_bw d) (Heter.lab trs) in
          return (Heter.leaf x)
      | Branch (_, _) :: _ ->
          let (Suc km') = km in
          let (Ends (hs, ends)) = Heter.ends trs in
          let mid = Heter.mid trs in
          let (Hgts newhs) = Heter.hgts_of_tlist cst in
          let* newends =
            BwvM.pmapM
              (fun (e :: brs) ->
                let* xs =
                  gpmapM km' (D.suc_plus lm) (End (e, d)) g (Heter.hgt_of_hlist hs brs) cst in
                return (Heter.hlist_of_hgt newhs xs))
              (Endpoints.indices :: ends) (Heter.tlist_hgts newhs cst) in
          let* newmid = gpmapM (D.suc_plus km) (D.suc_plus lm) (Mid d) g mid cst in
          return (Heter.branch newhs newends newmid)

    (* And the actual one for a t, which we can henceforth restrict our attention to. *)
    let pmapM :
        type n b bs cs.
        (n, (b, bs) cons, cs) pmapperM ->
        (n, n, (b, bs) cons) Heter.hgt ->
        cs Tlist.t ->
        (n, n, cs) Heter.hgt M.t =
     fun g xs cs ->
      let (x :: _) = xs in
      let n = dim x in
      gpmapM (D.zero_plus n) (D.zero_plus n) Zero g xs cs

    type ('n, 'bs, 'c) mmapperM = {
      map : 'm. ('m, 'n) sface -> ('m, 'bs) Heter.hft -> ('m, 'c) F.t M.t;
    }

    let mmapM :
        type n b bs c.
        (n, (b, bs) cons, c) mmapperM -> (n, n, (b, bs) cons) Heter.hgt -> (n, c) t M.t =
     fun g xs ->
      let* [ ys ] =
        pmapM
          {
            map =
              (fun fa x ->
                let* y = g.map fa x in
                (* Apparently writing [y] is insufficiently polymorphic *)
                return (y @: []));
          }
          xs (Cons Nil) in
      return ys

    type ('n, 'bs) miteratorM = { it : 'm. ('m, 'n) sface -> ('m, 'bs) Heter.hft -> unit M.t }

    let miterM :
        type n b bs. (n, (b, bs) cons) miteratorM -> (n, n, (b, bs) cons) Heter.hgt -> unit M.t =
     fun g xs ->
      let* [] =
        pmapM
          {
            map =
              (fun fa x ->
                let* () = g.it fa x in
                return hnil);
          }
          xs Nil in
      return ()

    (* The builder function isn't quite a special case of the generic traversal, since it needs to maintain different information when constructing a cube from scratch. *)

    type ('n, 'b) builderM = { build : 'm. ('m, 'n) sface -> ('m, 'b) F.t M.t }

    let rec gbuildM :
        type k m mk l ml b.
        m D.t ->
        (m, k, mk) D.plus ->
        (m, l, ml) D.plus ->
        (k, l) bwsface ->
        (ml, b) builderM ->
        (m, mk, b) gt M.t =
     fun m mk ml d g ->
      match m with
      | Nat Zero ->
          let Eq = D.plus_uniq mk (D.zero_plus (dom_bwsface d)) in
          let Eq = D.plus_uniq ml (D.zero_plus (cod_bwsface d)) in
          let* x = g.build (sface_of_bw d) in
          return (Leaf x)
      | Nat (Suc m) ->
          let (Suc mk') = D.plus_suc mk in
          let* ends =
            BwvM.mapM
              (fun e -> gbuildM (Nat m) mk' (D.plus_suc ml) (End (e, d)) g)
              Endpoints.indices in
          let* mid = gbuildM (Nat m) (D.plus_suc mk) (D.plus_suc ml) (Mid d) g in
          return (Branch (ends, mid))

    let buildM : type n b. n D.t -> (n, b) builderM -> (n, b) t M.t =
     fun n g -> gbuildM n (D.plus_zero n) (D.plus_zero n) Zero g
  end

  (* Now we can specialize all of them to the identity modality. *)

  module IdM = Monadic (Monad.Identity)

  let pmap :
      type n b bs cs.
      (n, (b, bs) cons, cs) IdM.pmapperM ->
      (n, n, (b, bs) cons) Heter.hgt ->
      cs Tlist.t ->
      (n, n, cs) Heter.hgt =
   fun g xs ys -> IdM.pmapM { map = (fun fa x -> g.map fa x) } xs ys

  let mmap :
      type n b bs c. (n, (b, bs) cons, c) IdM.mmapperM -> (n, n, (b, bs) cons) Heter.hgt -> (n, c) t
      =
   fun g xs -> IdM.mmapM { map = (fun fa x -> g.map fa x) } xs

  let miter :
      type n b bs. (n, (b, bs) cons) IdM.miteratorM -> (n, n, (b, bs) cons) Heter.hgt -> unit =
   fun g xs -> IdM.miterM { it = (fun fa x -> g.it fa x) } xs

  let build : type n b. n D.t -> (n, b) IdM.builderM -> (n, b) t =
   fun n g -> IdM.buildM n { build = (fun fa -> g.build fa) }

  (* Folds.  As with lists and bwvs, the ordinary left fold can be defined as a special case of the generic traversal. *)

  type ('n, 'c, 'b) fold_lefter = { fold : 'm. 'c -> ('m, 'n) sface -> ('m, 'b) F.t -> 'c }

  let fold_left : type n b c. (n, c, b) fold_lefter -> c -> (n, b) t -> c =
   fun g acc tr ->
    let open Monadic (Monad.State (struct
      type t = c
    end)) in
    snd (miterM { it = (fun fa [ x ] c -> ((), g.fold c fa x)) } [ tr ] acc)

  (* A "subcube" of a cube of dimension n, determined by a face of n with dimension k, is the cube of dimension k consisting of the elements indexed by faces that factor through the given one. *)
  let subcube : type m n b. (m, n) sface -> (n, b) t -> (m, b) t =
   fun fa tr -> build (dom_sface fa) { build = (fun fb -> find tr (comp_sface fa fb)) }
end

(* In the vast majority of cases, the second type parameter 'b in a Fam can just *be* the type of the elements.  The only case when this doesn't work is when the type has to also depend on the dimension 'a. *)
module FamOf = struct
  type ('a, 'b) t = 'b
end

module CubeOf = struct
  include Cube (FamOf)

  (* In this special case, we can change the indexing dimension fairly arbitrarily, although it takes a bit of work to convince OCaml.  (Of course, semantically these are identity functions.) *)

  let rec lift : type m n1 n2 n12 b. (n1, n2, n12) D.plus -> (m, n1, b) gt -> (m, n12, b) gt =
   fun n12 tr ->
    match tr with
    | Leaf x -> Leaf x
    | Branch (ends, mid) ->
        let (Suc n12') = N.plus_suc n12 in
        Branch (Bwv.map (fun t -> lift n12' t) ends, lift n12 mid)

  let rec lower :
      type m k n1 n2 n12 b.
      (m, k, n1) D.plus -> (n1, n2, n12) D.plus -> (m, n12, b) gt -> (m, n1, b) gt =
   fun mk n12 tr ->
    match (tr, n12) with
    | Leaf x, _ -> Leaf x
    | _, Zero -> tr
    | Branch (ends, mid), Suc n12' ->
        let mk' = N.plus_suc mk in
        let (Suc mk'') = mk' in
        Branch (Bwv.map (fun t -> lower mk'' (N.plus_suc n12') t) ends, lower mk' n12 mid)

  (* We can also extract the elements of a cube and append them to a Bwv. *)

  let rec gflatten_append :
      type k m km n b l len f lenf.
      (k, m, km) D.plus ->
      (l, m, n) D.plus ->
      (k, l) bwsface ->
      (b, len) Bwv.t ->
      (m, km, b) gt ->
      (m, f) count_faces ->
      (len, f, lenf) N.plus ->
      (b, lenf) Bwv.t =
   fun km lm d acc tr mf lenf ->
    match tr with
    | Leaf x ->
        let Zero, Zero = (km, lm) in
        let Eq = faces_uniq faces_zero mf in
        let (Suc Zero) = lenf in
        Snoc (acc, x)
    | Branch (ends, mid) ->
        let (Suc km') = km in
        let (Suc (mf', Suc (ft, pq))) = mf in
        let (Plus lenf') = N.plus (N.times_out ft) in
        let lenff = N.plus_assocl lenf' pq lenf in
        let acc =
          Bwv.fold_left2_bind_append ft lenf' acc Endpoints.indices ends
            {
              append =
                (fun pq cx e br -> gflatten_append km' (D.suc_plus lm) (End (e, d)) cx br mf' pq);
            } in
        gflatten_append (D.suc_plus km) (D.suc_plus lm) (Mid d) acc mid mf' lenff

  let flatten_append :
      type n b len f lenf.
      (b, len) Bwv.t -> (n, b) t -> (n, f) count_faces -> (len, f, lenf) N.plus -> (b, lenf) Bwv.t =
   fun acc tr mf lenf ->
    let n = dim tr in
    gflatten_append (D.zero_plus n) (D.zero_plus n) Zero acc tr mf lenf

  let flatten : type n b f. (n, b) t -> (n, f) count_faces -> (b, f) Bwv.t =
   fun tr mf ->
    let n = dim tr in
    gflatten_append (D.zero_plus n) (D.zero_plus n) Zero Emp tr mf (N.zero_plus (faces_out mf))

  (* Or, more simply, to a Bwd. *)
  let append_bwd : type a n. a Bwd.t -> (n, a) t -> a Bwd.t =
   fun start xs ->
    let module S = struct
      type t = a Bwd.t
    end in
    let module M = Monad.State (S) in
    let open Monadic (M) in
    let (), xs = miterM { it = (fun _ [ x ] xs -> ((), Snoc (xs, x))) } [ xs ] start in
    xs
end
