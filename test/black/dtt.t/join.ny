{` This file contains the construction of join of SSTs `}

` Unit type; use `()` to introduce an element.
def ⊤ : Type := sig ()

` Empty type.
def ⊥ : Type := data []

` Elimination principle for `⊥`; useful for when we cannot use an empty pattern
` match directly.
def absurd (A : Type) : ⊥ → A := []

` We define `Prod` as a separate record type to get better goals.
def Prod (A : Type) (B : Type) : Type :=
  sig (fst : A, snd : B)

notation 6 Prod : A "×" B := Prod A B

def Σ (A : Type) (B : A → Type) : Type :=
  sig (fst : A, snd : B fst)

` Coproducts.
def Coprod (A B : Type) : Type := data [
| inl. : A → Coprod A B
| inr. : B → Coprod A B
]

notation 5 Coprod : A "⊔" B := Coprod A B

def Coprod.rec (A B X : Type) (f : A → X) (g : B → X) : A ⊔ B → X := [
| inl. a ↦ f a
| inr. b ↦ g b
]

def Nat : Type := data [
| zero. : Nat
| suc. : Nat → Nat
]

` Degenerate a Nat into a Nat⁽ᵈ⁾.
def Nat.degen (n : Nat) : Nat⁽ᵈ⁾ n := match n [
| zero. ↦ zero.
| suc. n ↦ suc. (Nat.degen n)
]

` The "synthetic" gel operation; classifies `Type⁽ᵈ⁾ A` via a map into the universe.
def Gel (A : Type) : (A → Type) → Type⁽ᵈ⁾ A := A' ↦ sig x ↦ (ungel : A' x)

`````````````````````````````````````````````````````````````````````````````````````
`` Analytic semi-simplicial types.

` The type of semisimplicial types.
def SST : Type := codata [
| X .z : Type
| X .s : (X .z) → SST⁽ᵈ⁾ X
]

` Maps of semisimplicial types.
def Hom (X Y : SST) : Type := codata [
| f .z : X .z → Y .z
| f .s : (x : X .z) → Hom⁽ᵈ⁾ X (X .s x) Y (Y .s (f .z x)) f
]

def SST.id (X : SST) : Hom X X := [
| .z ↦ x ↦ x
| .s ↦ x ↦ SST.id⁽ᵈ⁾ X (X .s x)
]

` Trivially display a semisimplicial type over another SST.
def SST.const (X Y : SST) : SST⁽ᵈ⁾ X := [
| .z ↦ Gel (X .z) (x ↦ Y .z)
| .s ↦ x y ↦ sym (SST.const⁽ᵈ⁾ X (X .s x) Y (Y .s (y .ungel)))
]

` The terminal SST.
def SST.⊤ : SST := [
| .z ↦ ⊤
| .s ↦ _ ↦ SST.⊤⁽ᵈ⁾
]

` The initial SST.
def SST.⊥ : SST := [
| .z ↦ ⊥
| .s ↦ []
]

def SST.¡² (A B : SST) (f : Hom A B) (B' : SST⁽ᵈ⁾ B) : Hom⁽ᵈ⁾ A (SST.const A SST.⊥) B B' f :=
[
| .z ↦ a ff ↦ absurd (B' .z (f .z a)) (ff .ungel)
| .s ↦ a ff ↦
  absurd
    (Hom⁽ᵈᵈ⁾ A (SST.const A SST.⊥) (A .s a)
         (sym (SST.const⁽ᵈ⁾ A (A .s a) SST.⊥ (SST.⊥ .s (ff .ungel)))) B B'
         (B .s (f .z a))
         (B' .s (f .z a) (absurd (B' .z (f .z a)) (ff .ungel))) f
         (SST.¡² A B f B') (f .s a))
    (ff .ungel)
]

` Discrete SSTs
def Disc (X : Type) : SST := [
| .z ↦ X
| .s ↦ x ↦ Disc⁽ᵈ⁾ X (Gel X (_ ↦ ⊥))
]

` Universal property of `Disc X`; when specialized to `X = ⊤`, this gives
` us a simple form of the yoneda lemma for the 0th representable.
def よ₀ (X : Type) (A : SST) (a : X → A .z) : Hom (Disc X) A := [
| .z ↦ x ↦ a x
| .s ↦ x ↦
  よ₀⁽ᵈ⁾
    X (Gel X (_ ↦ ⊥))
    A (A .s (a x))
    a (x' ff ↦ absurd (A .s (a x) .z (a x')) (ff .ungel))
]

` The 0th representable semisimplex.
def Δ₀ : SST := Disc ⊤

def Join (A : SST) (B : SST) : SST := [
| .z ↦
  A .z ⊔ B .z
| .s ↦ [
  | inl. a ↦
    Join⁽ᵈ⁾
      A (A .s a)
      B (SST.const B SST.⊤)
  | inr. b ↦
    Join⁽ᵈ⁾
      A (SST.const A SST.⊥)
      B (B .s b)
  ]
]

{`
Trying to make Join.link arise as Hom (d?) of some sort of SST.
`}

` def Sec (A B C : SST) (f : Hom A C) : SST⁽ᵈ⁾ A := [
` | .z ↦ Hom B C
` | .s ↦ g ↦ Sec⁽ᵈ⁾ A ? B ? C ? f ?
` ]

` Vertical sections of a map; instead of having points over points, lines over lines, etc,
` we have points over points, lines over a point, triangles over a point, and so on.
def VSec (A B : SST) (f : Hom A B) : Type := codata [
| S .z : (b : B .z) → Hom⁽ᵈ⁾ A (SST.const A SST.⊤) B (B .s b) f
| S .s : (b : B .z) → VSec⁽ᵈ⁾ A (SST.const A SST.⊤) B (B .s b) f (S .z b) S
]

` Vertical sections restricted to the image of `f`.
def VSec.along (A B C : SST) (f : Hom A C) (g : Hom B C) : Type := codata [
| S .z : (a : A .z) → Hom⁽ᵈ⁾ B (SST.const B SST.⊤) C (C .s (f .z a)) g
| S .s : (a : A .z) →
  VSec.along⁽ᵈ⁾
    A (A .s a)
    B (SST.const B SST.⊤)
    C (C .s (f .z a))
    f (f .s a)
    g (S .z a) S
]

def VSec.disc_along
  (X : Type) (A B : SST)
  (f : X → B .z)
  (g : Hom A B)
  (s : (x : X) → Hom⁽ᵈ⁾ A (SST.const A SST.⊤) B (B .s (f x)) g)
  : VSec.along (Disc X) A B (よ₀ X B f) g :=
[
| .z ↦ x ↦ s x
| .s ↦ x ↦
  VSec.disc_along⁽ᵈ⁾
    X (Gel X (_ ↦ ⊥))
    A (SST.const A SST.⊤)
    B (B .s (f x))
    f (x' ff ↦ absurd (B .s (f x) .z (f x')) (ff .ungel))
    g (s x)
    s (x' ff ↦
      absurd
        (Hom⁽ᵈᵈ⁾ A (SST.const A SST.⊤) (SST.const A SST.⊤)
         (SST.const⁽ᵈ⁾ A (SST.const A SST.⊤) SST.⊤ SST.⊤⁽ᵈ⁾) B (B .s (f x))
         (B .s (f x'))
         (B .s (f x) .s (f x') (absurd (B .s (f x) .z (f x')) (ff .ungel))) g
         (s x) (s x'))
         (ff .ungel))
]

` NOTE: This can probably be generalized to a general result about
` extending vertical sections, but it is easier to just refute everything.
def VSec.absurd_along
  (A : SST) (B : SST) (C : SST)
  (f : Hom A C) (g : Hom B C)
  (b : B .z)
  (s : VSec.along A B C f g)
  : VSec.along⁽ᵈ⁾
      A (SST.const A SST.⊥)
      B (B .s b)
      C (C .s (g .z b))
      f (SST.¡² A C f (C .s (g .z b)))
      g (g .s b)
      s
  :=
[
| .z ↦ a ff ↦
  absurd
    (Hom⁽ᵈᵈ⁾ B (B .s b) (SST.const B SST.⊤)
         (SST.const⁽ᵈ⁾ B (B .s b) SST.⊤ SST.⊤⁽ᵈ⁾) C (C .s (g .z b))
         (C .s (f .z a))
         (C .s (g .z b) .s (f .z a)
            (absurd (C .s (g .z b) .z (f .z a)) (ff .ungel))) g (g .s b)
         (s .z a))
    (ff .ungel)
| .s ↦ a ff ↦
    absurd
      (VSec.along⁽ᵈᵈ⁾ A (SST.const A SST.⊥) (A .s a)
         (sym (SST.const⁽ᵈ⁾ A (A .s a) SST.⊥ (SST.⊥ .s (ff .ungel)))) B
         (B .s b) (SST.const B SST.⊤)
         (SST.const⁽ᵈ⁾ B (B .s b) SST.⊤ SST.⊤⁽ᵈ⁾) C (C .s (g .z b))
         (C .s (f .z a))
         (C .s (g .z b) .s (f .z a)
            (absurd (C .s (g .z b) .z (f .z a)) (ff .ungel))) f
         (SST.¡² A C f (C .s (g .z b))) (f .s a)
         (absurd
            (Hom⁽ᵈᵈ⁾ A (SST.const A SST.⊥) (A .s a)
               (sym (SST.const⁽ᵈ⁾ A (A .s a) SST.⊥ (SST.⊥ .s (ff .ungel)))) C
               (C .s (g .z b)) (C .s (f .z a))
               (C .s (g .z b) .s (f .z a)
                  (absurd (C .s (g .z b) .z (f .z a)) (ff .ungel))) f
               (SST.¡² A C f (C .s (g .z b))) (f .s a)) (ff .ungel)) g
         (g .s b) (s .z a)
         (absurd
            (Hom⁽ᵈᵈ⁾ B (B .s b) (SST.const B SST.⊤)
               (SST.const⁽ᵈ⁾ B (B .s b) SST.⊤ SST.⊤⁽ᵈ⁾) C (C .s (g .z b))
               (C .s (f .z a))
               (C .s (g .z b) .s (f .z a)
                  (absurd (C .s (g .z b) .z (f .z a)) (ff .ungel))) g
               (g .s b) (s .z a)) (ff .ungel)) s
         (VSec.absurd_along A B C f g b s) (s .s a))
       (ff .ungel)
]

def Join.rec
  (A B C : SST)
  (f : Hom A C)
  (g : Hom B C)
  (s : VSec.along A B C f g)
  : Hom (Join A B) C
  :=
[
| .z ↦ [
  | inl. a ↦ f .z a
  | inr. b ↦ g .z b
  ]
| .s ↦ [
  | inl. a ↦
    Join.rec⁽ᵈ⁾
      A (A .s a)
      B (SST.const B SST.⊤)
      C (C .s (f .z a))
      f (f .s a)
      g (s .z a)
      s (s .s a)
  | inr. b ↦
    Join.rec⁽ᵈ⁾
      A (SST.const A SST.⊥)
      B (B .s b)
      C (C .s (g .z b))
      f (SST.¡² A C f (C .s (g .z b)))
      g (g .s b)
      s (VSec.absurd_along A B C f g b s)
  ]
]

def Join.inl
  (A B : SST)
  : Hom A (Join A B)
  :=
[
| .z ↦ a ↦ inl. a
| .s ↦ a ↦ Join.inl⁽ᵈ⁾ A (A .s a) B (SST.const B SST.⊤)
]

def Join.inr
  (A B : SST)
  : Hom B (Join A B)
  :=
[
| .z ↦ b ↦ inr. b
| .s ↦ b ↦ Join.inr⁽ᵈ⁾ A (SST.const A SST.⊥) B (B .s b)
]

def Cone (A : SST) : SST := Join Δ₀ A
def Cocone (A : SST) : SST := Join A Δ₀

def Cone.rec
  (A B : SST)
  (pt : B .z)
  (f : Hom A B)
  (s : Hom⁽ᵈ⁾ A (SST.const A SST.⊤) B (B .s pt) f)
  : Hom (Cone A) B
  :=
    Join.rec
      Δ₀ A B
      (よ₀ ⊤ B (_ ↦ pt))
      f
      (VSec.disc_along ⊤ A B (_ ↦ pt) f (_ ↦ s))

` Generalized representables.
def Δ : Nat → SST := [
| zero. ↦ Δ₀
| suc. n ↦ Cone (Δ n)
]

def VHom (X : SST) (X' Y' : SST⁽ᵈ⁾ X) : Type := codata [
| f .z : (x : X .z) → X' .z x → Y' .z x
| f .s :
  (x : X .z) (x' : X' .z x) →
  VHom⁽ᵈ⁾ X (X .s x) X' (sym (X' .s x x')) Y' (sym (Y' .s x (f .z x x'))) f
]

` The type of global elements of a simplex.
def Pt (A : SST) : Type := codata [
| p .z : A .z
| p .s : Pt⁽ᵈ⁾ A (A .s (p .z)) p
]

` Build a global element from a map.
def Pt.global (A : SST) (f : Hom SST.⊤ A) : Pt A := [
| .z ↦ f .z ()
| .s ↦ Pt.global⁽ᵈ⁾ A (A .s (f .z ())) f (f .s ())
]

` Take the fibre of a displayed SST at a point.
def Fibre (A : SST) (A' : SST⁽ᵈ⁾ A) (a : Pt A) : SST := [
| .z ↦ A' .z (a .z)
| .s ↦ a' ↦ Fibre⁽ᵈ⁾ A (A .s (a .z)) A' (sym (A' .s (a .z) a')) a (a .s)
]

def ∫ (A : SST) (A' : SST⁽ᵈ⁾ A) : SST := [
| .z ↦ Σ (A .z) (a ↦ A' .z a)
| .s ↦ ∫a ↦ ∫⁽ᵈ⁾ A (A .s (∫a .fst)) A' (sym (A' .s (∫a .fst) (∫a .snd)))
]

def SST.comp (A : SST) (B : SST⁽ᵈ⁾ A) (C : SST⁽ᵈ⁾ (∫ A B)) : SST⁽ᵈ⁾ A := [
| .z ↦ Gel (A .z) (a ↦ Σ (B .z a) (b ↦ C .z (a, b)))
| .s ↦ a bc ↦
  sym (SST.comp⁽ᵈ⁾
    A (A .s a)
    B (sym (B .s a (bc .ungel .fst)))
    C (sym (C .s (a , bc .ungel .fst) (bc .ungel .snd))))
]

