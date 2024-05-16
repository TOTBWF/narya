{` Prelude `}

def ⊥ : Type := data []
def ⊤ : Type := sig ()

def absurd (A : Type) : ⊥ → A := []

def Nat : Type := data [
| zero. : Nat
| succ. : Nat → Nat
]

def Σ (A : Type) (B : A → Type) : Type :=
  sig (fst : A, snd : B fst)

def coprod (A B : Type) : Type := data [
| inl. : A → coprod A B
| inr. : B → coprod A B
]

def Maybe (A : Type) : Type := data [
| some. : A → Maybe A
| none. : Maybe A
]

def Maybe.rec (A X : Type) (x : X) (f : A → X) : Maybe A → X := [
| none. ↦ x
| some. a ↦ f a
]

notation 5 coprod : A "+" B := coprod A B

def Coprod.rec (A B X : Type) (f : A → X) (g : B → X) : A + B → X := [
| inl. a ↦ f a
| inr. b ↦ g b
]
` The "synthetic" gel operation; classifies `Type⁽ᵈ⁾ A` via a map into the universe.
def SGel (A : Type) : (A → Type) → Type⁽ᵈ⁾ A := A' ↦ sig x ↦ (ungel : A' x)

def SGel²
  (Ap : Type) (Ax Ay : Type⁽ᵈ⁾ Ap)
  (Aα : (p : Ap) → Ax p → Ay p → Type)
  : Type⁽ᵈᵈ⁾ Ap Ax Ay := sig p x y ↦ (ungel : Aα p x y)

` Note that "synthetic" ungel is simply application. Note that SGel/UnSGel do not
` form an isomorphism, but they *do* form a retract (up to definitional ismorphism).
def UnSGel (A : Type) : Type⁽ᵈ⁾ A → (A → Type) := A' a ↦ A' a

` Introduction form for synthetic gel. This is present so that we can compare
` against the analytic version; users should just write `ungel := ?` directly.
def SGel.intro (A : Type) (A' : A → Type) (x : A) : A' x → UnSGel A (SGel A A') x :=
  x' ↦ (ungel := x')

` Elimination form for synthetic gel. This is present so that we can compare
` against the analytic version; users should just write `? .ungel` directly.
def SGel.elim (A : Type) (A' : A → Type) (x : A) : SGel A A' x → A' x :=
  x' ↦ x' .ungel

{` Augmented Simplices `}

def ASST : Type := codata [
| X .z : Type
| X .s : ASST⁽ᵈ⁾ X
]

` Maps of augmented simplicies.
def Hom (A B : ASST) : Type := codata [
| f .z : A .z → B .z
| f .s : Hom⁽ᵈ⁾ A (A .s) B (B .s) f
]

` The type of global elements of `A`.
` This could be represented as `Hom ASST.⊤ A`, but this definition is nicer to use.
def ASST.pt (A : ASST) : Type := codata [
| p .z : A .z
| p .s : ASST.pt⁽ᵈ⁾ A (A .s) p
]

def ASST.fhom (A : ASST) (A' B' : ASST⁽ᵈ⁾ A) : Type := codata [
| f .z : (a : A .z) → A' .z a → B' .z a
| f .s : ASST.fhom⁽ᵈ⁾ A (A .s) A' (sym (A' .s)) B' (sym (B' .s)) f
]

def Fam² (Ap : ASST) (Ax Ay : ASST⁽ᵈ⁾ Ap) : Type := codata [
| f .z : (p : Ap .z) → Ax .z p → Ay .z p → Type
| f .s : Fam²⁽ᵈ⁾ Ap (Ap .s) Ax (sym (Ax .s)) Ay (sym (Ay .s)) f
]

def ASST.fpullback
  (A : ASST) (A' B' : ASST⁽ᵈ⁾ A)
  (f : ASST.fhom A A' B')
  (A'' : ASST⁽ᵈᵈ⁾ A B' B') :
  ASST⁽ᵈᵈ⁾ A A' A' :=
[
| .z ↦ SGel² (A .z) (A' .z) (A' .z) ?
`SGel⁽ᵈ⁾ (A .z) (A' .z) (a ↦ A' .z a) (a a' ↦ ?)
| .s ↦ ?
]

` def ASST.Hom (A B : ASST) : ASST := [
` | .z ↦ A .z → B .z
` | .s ↦ ASST.Hom⁽ᵈ⁾ A (A .s) B (B .s)
` ]

` The ASST of types.
def 𝒰 : ASST := [
| .z ↦ Type
| .s ↦ 𝒰⁽ᵈ⁾
]

` def ASST.align (A : ASST) (A' : Hom A 𝒰) (p : ASST.pt A) : ASST := [
` | .z ↦ A' .z (p .z)
` | .s ↦ ASST.align⁽ᵈ⁾ A (A .s) A' (A' .s) p (p .s)
` ]

` Analytic gel; witnesses 𝒰 as a weak classifying object for `ASST⁽ᵈ⁾ A`.
def AGel (A : ASST) (A' : Hom A 𝒰) : ASST⁽ᵈ⁾ A := [
| .z ↦ SGel (A .z) (a ↦ A' .z a)
| .s ↦ sym (AGel⁽ᵈ⁾ A (A .s) A' (A' .s))
]

def AGel² (Ap : ASST) (Ax Ay : ASST⁽ᵈ⁾ Ap) (Aα : Fam² Ap Ax Ay) : ASST⁽ᵈᵈ⁾ Ap Ax Ay := [
| .z ↦ SGel² (Ap .z) (Ax .z) (Ay .z) (Aα .z)
| .s ↦ (AGel²⁽ᵈ⁾ Ap (Ap .s) Ax (sym (Ax .s)) Ay (sym (Ay .s)) Aα (Aα .s))⁽²³¹⁾
]

` ` Analytic ungel.
` def AUnGel (A : ASST) (A' : ASST⁽ᵈ⁾ A) : Hom A 𝒰 := [
` | .z ↦ a ↦ A' .z a
` | .s ↦ AUnGel⁽ᵈ⁾ A (A .s) A' (sym (A' .s))
` ]

def Cocone (A : ASST) : ASST := [
| .z ↦ A .z
| .s ↦
[
  | .z ↦ SGel (A .z) (a ↦ A .z + A .s .z a)
  | .s ↦ Cocone⁽ᵈᵈ⁾ A (A .s) (A .s) (A .s .s)
  ]
]
`AGel (Cocone A) (Cocone.fib A)


and Cocone.fib (A : ASST) : Hom (Cocone A) 𝒰 := [
| .z ↦ a ↦ A .z + A .s .z a
| .s ↦ Cocone.fib⁽ᵈ⁾ A (A .s)
]

{`
Big Picture:
Cannot do constructions that require 2 nested iterations!
Big problem seems to be that we can construct things like Blah⁽ᵈᵈ⁾ ... with trailing ⁽ᵈ⁾'d things,
but the typechecker wants those things to be .s'd

What we've tried:
* One possible solution is some sort of "analytic gel", which tries to avoid the double ⁽ᵈᵈ⁾ by
using some sort of classifying object; this lets us work only under a single ⁽ᵈ⁾ at all times,
which ideally would avoid the introduction of the .s. However, this fails, as the goal type will
eventually be something like `Hom⁽ᵈ⁾ A (AUngel ...) B ...`, whereas we have `Hom⁽ᵈ⁾ A (A⁽ᵈ⁾ ...)`.
In `Type`, this would be solved via a lambda abstraction + a call to `ungel` (See Cocone.extend in
`quasi.ny`), but we cannot write the ASST version of this function over an arbitrary ASST.


`}
