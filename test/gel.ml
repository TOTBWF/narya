open Pmp

let () = Narya.Gel.install ()
let gEL, gELty = synth !~"GEL"

let gELty', _ =
  synth (pi "X" UU (pi "Y" UU (pi "R" (pi "x" !!"X" (pi "y" !!"Y" UU)) (id UU !!"X" !!"Y"))))

let () = equal gELty gELty'
let gel, gelty = synth !~"gel"

let gelty', _ =
  synth
    (pi "X" UU
       (pi "Y" UU
          (pi "R"
             (pi "x" !!"X" (pi "y" !!"Y" UU))
             (pi "x" !!"X"
                (pi "y" !!"Y"
                   (pi "r"
                      (!!"R" $ !!"x" $ !!"y")
                      (!~"GEL" $ !!"X" $ !!"Y" $ !!"R" $ !!"x" $ !!"y")))))))

let () = equal gelty gelty'
let ungel, ungelty = synth !~"ungel"

let ungelty', _ =
  synth
    (pi "X" UU
       (pi "Y" UU
          (pi "R"
             (pi "x" !!"X" (pi "y" !!"Y" UU))
             (pi "x" !!"X"
                (pi "y" !!"Y"
                   (pi "r"
                      (!~"GEL" $ !!"X" $ !!"Y" $ !!"R" $ !!"x" $ !!"y")
                      (!!"R" $ !!"x" $ !!"y")))))))

let () = equal ungelty ungelty'

(* Now we test ungel(gel) *)

let uu, _ = synth UU
let aa = assume "A" uu
let bb = assume "B" uu
let corrab, _ = synth (pi "x" !!"A" (pi "y" !!"B" UU))
let rr = assume "R" corrab
let a = assume "a" aa
let b = assume "b" bb
let _, corrab' = synth !!"R"
let () = equal corrab corrab'
let rab, _ = synth (!!"R" $ !!"a" $ !!"b")
let r = assume "r" rab

let r', _ =
  synth
    (!~"ungel"
    $ !!"A"
    $ !!"B"
    $ !!"R"
    $ !!"a"
    $ !!"b"
    $ (!~"gel" $ !!"A" $ !!"B" $ !!"R" $ !!"a" $ !!"b" $ !!"r"))

let () = equal r r'

(* and gel(ungel) *)

let gelab, _ = synth (!~"GEL" $ !!"A" $ !!"B" $ !!"R" $ !!"a" $ !!"b")
let s = assume "s" gelab

let s', _ =
  synth
    (!~"gel"
    $ !!"A"
    $ !!"B"
    $ !!"R"
    $ !!"a"
    $ !!"b"
    $ (!~"ungel" $ !!"A" $ !!"B" $ !!"R" $ !!"a" $ !!"b" $ !!"s"))

let () = equal s s'
