`````````````````````````````````````````````````````````````````````````````````````
`` Prelude.

` Unit type; use `()` to introduce an element.
def ⊤ : Type := sig ()

` Empty type.
def ⊥ : Type := data []

` Elimination principle for `⊥`; useful for when we cannot use an empty pattern
` match directly.
def absurd (A : Type) : ⊥ → A := []

def Nat : Type := data [
| zero. : Nat
| suc. : Nat → Nat
]


` Degenerate a Nat into a Nat⁽ᵈ⁾.
def Nat.degen (n : Nat) : Nat⁽ᵈ⁾ n := match n [
| zero. ↦ zero.
| suc. n ↦ suc. (Nat.degen n)
]

def Σ (A : Type) (B : A → Type) : Type :=
  sig (fst : A, snd : B fst)

` We define `Prod` as a separate record type to get better goals.
def Prod (A : Type) (B : Type) : Type :=
  sig (fst : A, snd : B)

notation 6 Prod : A "×" B := Prod A B

` Coproducts.
def Coprod (A B : Type) : Type := data [
| inl. : A → Coprod A B
| inr. : B → Coprod A B
]

notation 5 Coprod : A "+" B := Coprod A B

` Recursor for coproducts.
def Coprod.rec (A B X : Type) (f : A → X) (g : B → X) : A + B → X := [
| inl. a ↦ f a
| inr. b ↦ g b
]

` We define `Maybe` separately to get better goals.
def Maybe (A : Type) : Type := data [
| some. : A → Maybe A
| none. : Maybe A
]

` Recursor for `Maybe`.
def Maybe.rec (A X : Type) (x : X) (f : A → X) : Maybe A → X := [
| none. ↦ x
| some. a ↦ f a
]


` The "synthetic" gel operation; classifies `Type⁽ᵈ⁾ A` via a map into the universe.
def Gel (A : Type) : (A → Type) → Type⁽ᵈ⁾ A := A' ↦ sig x ↦ (ungel : A' x)

` Typically, users should write `(ungel := x)` to introduce an element of `Gel`.
` This will not work when the gel type is underneath a `sym` for bidirectionality
` reasons, so we provide an explicit introduction form as well.
def Gel.intro (A : Type) (A' : A → Type) (x : A) (x' : A' x) : Gel A A' x :=
  (ungel := x')

` Two-dimensional gel.
def SGel²
  (Ap : Type) (Ax Ay : Type⁽ᵈ⁾ Ap)
  (Aα : (p : Ap) → Ax p → Ay p → Type)
  : Type⁽ᵈᵈ⁾ Ap Ax Ay := sig p x y ↦ (ungel : Aα p x y)

`````````````````````````````````````````````````````````````````````````````````````
`` Analytic semi-simplicial types.

` Semi
def SST : Type := codata [
| X .z : Type
| X .s : (X .z) → SST⁽ᵈ⁾ X
]

def Hom (X Y : SST) : Type := codata [
| f .z : X .z → Y .z
| f .s : (x : X .z) → Hom⁽ᵈ⁾ X (X .s x) Y (Y .s (f .z x)) f
]

` "Vertical" homs that have better definitional compositions.
def VHom (X : SST) (X' Y' : SST⁽ᵈ⁾ X) : Type := codata [
| f .z : (x : X .z) → X' .z x → Y' .z x
| f .s : (x : X .z) (x' : X' .z x) → VHom⁽ᵈ⁾ X (X .s x) X' (sym (X' .s x x')) Y' (sym (Y' .s x (f .z x x'))) f
]

def Hom.comp (X Y Z : SST) (f : Hom X Y) (g : Hom Y Z) : Hom X Z := ?

def Hom.vcompl
  (X Y : SST)
  (X' X'' : SST⁽ᵈ⁾ X) (Y' : SST⁽ᵈ⁾ Y)
  (f : VHom X X' X'')
  (g : Hom X Y) (g' : Hom⁽ᵈ⁾ X X'' Y Y' g)
  : Hom⁽ᵈ⁾ X X' Y Y' g := ?

def Sec (X : SST) (Y : SST⁽ᵈ⁾ X) : Type := codata [
| S .z : (x : X .z) → Y .z x
| S .s : (x : X .z) → Sec⁽ᵈ⁾ X (X .s x) Y (sym (Y .s x (S .z x))) S
]

def SST.const (X Y : SST) : SST⁽ᵈ⁾ X := [
| .z ↦ Gel (X .z) (x ↦ Y .z) `sig _ ↦ ( ungel : Y .z )
| .s ↦ x y ↦ sym (SST.const⁽ᵈ⁾ X (X .s x) Y (Y .s (y .ungel)))
]

def SST.pullback (X Y : SST) (f : Hom X Y) (Y' : SST⁽ᵈ⁾ Y) : SST⁽ᵈ⁾ X := [
| .z ↦ Gel (X .z) (x ↦ Y' .z (f .z x))
| .s ↦ x x' ↦
  sym (SST.pullback⁽ᵈ⁾ X (X .s x)
    Y (Y .s (f .z x))
    f (f .s x)
    Y' (sym (Y' .s (f .z x) (x' .ungel))))
]

def SST.⊤ : SST := [
| .z ↦ ⊤
| .s ↦ _ ↦ SST.⊤⁽ᵈ⁾
]

def SST.⊥ : SST := [
| .z ↦ ⊥
| .s ↦ []
]

def SST.¡ᵛ (A : SST) (A' : SST⁽ᵈ⁾ A) : VHom A (SST.const A SST.⊥) A' := ?

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



def Disc (X : Type) : SST := [
| .z ↦ X
| .s ↦ x ↦ SST.const (Disc X) SST.⊥ `Disc⁽ᵈ⁾ X (Gel X (_ ↦ ⊥))
]

def Disc.gel (X Y : Type)
  : VHom (Disc X) (SST.const (Disc X) (Disc Y)) (Disc⁽ᵈ⁾ X (Gel X (_ ↦ Y)))
  := [
| .z ↦ x y ↦ (ungel := y .ungel)
| .s ↦ x y ↦ ?
]

       ` VHom (Disc X) (SST.const (Disc X) (Disc ⊤))
       `   (Disc⁽ᵈ⁾ X (Gel X (_ ↦ ⊤)))

def Δ₀ : SST := Disc ⊤

def よ₀ (X : Type) (A : SST) (a : X → A .z) : Hom (Disc X) A := [
| .z ↦ x ↦ a x
| .s ↦ x ↦ SST.¡² (Disc X) A (よ₀ X A a) (A .s (a x))
]

def Join (X : Type) (A : SST) (B : SST) : SST := [
| .z ↦ (X × A .z) + B .z
| .s ↦ [
  | inl. xa ↦ Join⁽ᵈ⁾ X (Gel X (_ ↦ ⊥)) A (A .s (xa .snd)) B (SST.const B (Disc X))
  | inr. b ↦ Join⁽ᵈ⁾ X (Gel X (_ ↦ ⊥)) A (SST.const A SST.⊥) B (B .s b)
  ]
]

def Cone (X : Type) (A : SST) : SST := Join X Δ₀ A
def Cocone (X : Type) (A : SST) : SST := Join X A Δ₀

def Join.rec
  (X : Type) (A B T : SST)
  (f : Hom A T) (g : Hom B T)
  (s : (xa : X × A .z) → Hom⁽ᵈ⁾ B (SST.const B (Disc X)) T (T .s (f .z (xa .snd))) g)
  : Hom (Join X A B) T :=
[
| .z ↦ [
  | inl. xa ↦ f .z (xa .snd)
  | inr. b ↦ g .z b
  ]
| .s ↦ [
  | inl. xa ↦
    Join.rec⁽ᵈ⁾
      X (Gel X (_ ↦ ⊥))
      A (A .s (xa .snd))
      B (SST.const B (Disc X))
      T (T .s (f .z (xa .snd)))
      f (f .s (xa .snd))
      g (s xa)
      s (xa' ff ↦
        absurd
          (Hom⁽ᵈᵈ⁾
            B (SST.const B (Disc X)) (SST.const B (Disc X))
            (SST.const⁽ᵈ⁾ B (SST.const B (Disc X)) (Disc X) (Disc⁽ᵈ⁾ X (Gel X (_ ↦ ⊥))))
            T (T .s (f .z (xa .snd))) (T .s (f .z (xa' .snd)))
            (T .s (f .z (xa .snd)) .s (f .z (xa' .snd)) (f .s (xa .snd) .z (xa' .snd) (ff .snd)))
            g (s xa) (s xa'))
        (ff .fst .ungel))
  | inr. b ↦
    Join.rec⁽ᵈ⁾
      X (Gel X (_ ↦ ⊥))
      A (SST.const A SST.⊥)
      B (B .s b)
      T (T .s (g .z b))
      f (SST.¡² A T f (T .s (g .z b)))
      g (g .s b)
      s (xa' ff ↦
        absurd
          (Hom⁽ᵈᵈ⁾ B (B .s b) (SST.const B (Disc X))
           (SST.const⁽ᵈ⁾ B (B .s b) (Disc X) (Disc⁽ᵈ⁾ X (Gel X (_ ↦ ⊥)))) T
         (T .s (g .z b)) (T .s (f .z (xa' .snd)))
         (T .s (g .z b) .s (f .z (xa' .snd))
            (absurd (T .s (g .z b) .z (f .z (xa' .snd))) (ff .snd .ungel))) g
         (g .s b) (s xa'))
        (ff .fst .ungel))
  ]
]

def Join.inr
  (X : Type)
  (A B : SST)
  : Hom B (Join X A B)
  := ?

def Cone.rec
  (X : Type)
  (A B : SST)
  (f : Hom A B) (pt : B .z)
  (s : Hom⁽ᵈ⁾ A (SST.const A (Disc X)) B (B .s pt) f)
  : Hom (Cone X A) B
  := Join.rec X Δ₀ A B (よ₀ ⊤ B (_ ↦ pt)) f (_ ↦ s)

` The displayed SST of data over `a`.
def SST.over (A : SST) (a : A .z) : SST⁽ᵈ⁾ A := [
| .z ↦ Gel (A .z) (b ↦ A .s b .z a)
| .s ↦ b α ↦ sym (SST.over⁽ᵈ⁾ A (A .s b) a (α .ungel))
]

` The opposite SST.
def SST.op (A : SST) : SST := [
| .z ↦ A .z
| .s ↦ a ↦ SST.op⁽ᵈ⁾ A (SST.over A a)
]

` Representables.
def Δ (X : Type) : Nat → SST := [
| zero. ↦ Disc X
| suc. n ↦ Cone ⊤ (Δ X n)
]

def Δ.gel (X : Type) (n : Nat)
  : VHom (Δ X n) (SST.const (Δ X n) (Disc ⊤)) (Δ⁽ᵈ⁾ X (Gel X (_ ↦ ⊤)) n (Nat.degen n))
  := match n [
| zero. ↦ Disc.gel X ⊤
| suc. n ↦ [
  | .z ↦ x x' ↦ match x [
    | inl. tt ↦ inl. ((), ())
    | inr. x ↦ inr. (Δ.gel X n .z x (ungel := ())) `(Δ.gel⁽ᵈ⁾ X (Gel X (_ ↦ ⊤)) n (Nat.degen n) .z x ? ? ?)
  ]
  | .s ↦ x x' ↦ match x [
    | inl. tt ↦ ?
    ` NOTE: These all follow by a series of brutal `absurd` calls.
    ` If we had a built-in "kinetic absurd" that (a) lived in check and (b) could work with terms,
    ` then this headache could be avoided.
    `
    ` The other option is to build-in ⊥ as a built-in with an eliminator that was in "check".
    ` [
    `   | .z ↦ y y' z z' ↦ ? `z' .ungel .ungel
    `   | .s ↦ y y' z z' ↦ ? `z' .ungel .ungel
    ` ]
    | inr. x ↦ ?
    ` [
    `   | .z ↦ y y' z z' ↦ ? `z' .ungel .ungel
    `   | .s ↦ y y' z z' ↦ ? `z' .ungel .ungel
    ` ]
  ]
  ]
]

` The type of generalized n-dimensional boundaries in an SST `A`.
def ○ (X : Type) (n : Nat) (A : SST) : Type := match n [
| zero. ↦ X
| suc. n ↦
  sig
    (pt : A .z
    , ∂a : ○ X n A
    , a : ● X n A ∂a
    , ∂a' : ○⁽ᵈ⁾ X (Gel X (_ ↦ ⊤)) n (Nat.degen n) A (A .s pt) ∂a
    )
]

` The type of generalized n-dimensional boundary fillers in an SST `A`.
and ● (X : Type) (n : Nat) (A : SST) (○a : ○ X n A) : Type := match n [
| zero. ↦ X → A .z
| suc. n ↦ ●⁽ᵈ⁾ X (Gel X (_ ↦ ⊤)) n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a') (○a .a)
]

def 𝒰 (X : Type) : SST := [
| .z ↦ X → Type
| .s ↦ X' ↦ 𝒰⁽ᵈ⁾ X (Gel X X')
]

` Analytic yoneda: a boundary and a filler yields a generalized simplex in A.
def よ (X : Type) (A : SST) (n : Nat) (○a : ○ X n A) (a : ● X n A ○a) : Hom (Δ X n) A := match n [
| zero. ↦ よ₀ X A a
| suc. n ↦
  Cone.rec ⊤ (Δ X n) A
    (よ X A n (○a .∂a) (○a .a))
    (○a .pt)
    ?
    ` This is morally correct, but a bit of golf with Hom.vcompr + Δ.gel is required.
    `(よ⁽ᵈ⁾ X (Gel X (_ ↦ ⊤)) A (A .s (○a .pt)) n (Nat.degen n) (○a .∂a) (○a .∂a') (○a .a) a)
]

` axiom X : Type
` axiom x : X


` ` Tests:
` axiom A : SST
` axiom x : A .z
` axiom y : A .z
` axiom α : A .s x .z y
` axiom z : A .z
` axiom β : A .s x .z z
` axiom γ : A .s y .z z
` axiom f : A .s x .s y α .z z β γ

` def ○xy : ○ 1 A := (pt := x, ∂a := (), a := y, ∂a' := ())
` def ●xy : ● 1 A ○xy := α

` def ○yz : ○ 1 A := (pt := y, ∂a := (), a := z, ∂a' := ())
` def ●yz : ● 1 A ○yz := γ

` def ○αβ : ○⁽ᵈ⁾ 1 1 A (A .s x) ○yz := (pt := α, ∂a := (), a:= β, ∂a' := ())
` def ●αβ : ●⁽ᵈ⁾ 1 1 A (A .s x) ○yz ○αβ ●yz := f

` def ○αβγ : ○ 2 A := (pt := x, ∂a := ○yz, a := ●yz, ∂a' := ○αβ)
` def ●αβγ : ● 2 A ○αβγ := ●αβ

` ` Inline definition of all of the above data. Note the ordering!
` def ○αβγ' : ○ 2 A := (x, (y, (), z, ()), γ, (α, (), β, ()))
` def ●αβγ' : ● 2 A ○αβγ := f


` Lesson learned:
` * Never, ever, ever use ⊤ when doing coinductive definitions.
