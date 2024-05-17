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

` The biggest flamewar of all time; does induction proceed on the left, or on the right?
` There is a clearly correct answer that we will let the reader decide.
def Nat.add (n : Nat) : Nat → Nat := [
| zero. ↦ n
| suc. k ↦ suc. (Nat.add n k)
]

` Predecessor.
def Nat.pred : Nat → Nat := [
| zero. ↦ zero.
| suc. n ↦ n
]

notation 5 Nat.add : n "+" k := Nat.add n k

` Ordering on natural numbers.
def Nat.lte (k n : Nat) : Type := match k [
| zero. ↦ ⊤
| suc. k ↦ match n [
  | zero. ↦ ⊥
  | suc. n ↦ Nat.lte k n
  ]
]

` The strict order is defined in terms of non-strict order.
def Nat.lt (k n : Nat) : Type := Nat.lte (suc. k) n

notation 5 Nat.lte : k "≤" n := Nat.lte k n
notation 5 Nat.lt : k "<" n := Nat.lt k n

` Degenerate a proof that `k ≤ n`.
def Nat.lte.degen
  (k n : Nat)
  (h : k ≤ n)
  : Nat.lte⁽ᵈ⁾ k (Nat.degen k) n (Nat.degen n) h := match k [
| zero. ↦ ()
| suc. k ↦ match n [
  | zero. ↦ absurd (⊥⁽ᵈ⁾ h) h
  | suc. n ↦ Nat.lte.degen k n h
  ]
]

` Weaken a proof that `k ≤ n`.
def Nat.lte.wk (k n : Nat) (h : k ≤ n) : k ≤ suc. n := match k [
| zero. ↦ ()
| suc. k ↦ match n [
  | zero. ↦ absurd (k ≤ 0) h
  | suc. n ↦ Nat.lte.wk k n h
  ]
]

` Sigma types.
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

notation 5 Coprod : A "⊔" B := Coprod A B

` Recursor for coproducts.
def Coprod.rec (A B X : Type) (f : A → X) (g : B → X) : A ⊔ B → X := [
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

` Vertically displayed maps that have better definitional compositions than Hom⁽ᵈ⁾
def VHom (X : SST) (X' Y' : SST⁽ᵈ⁾ X) : Type := codata [
| f .z : (x : X .z) → X' .z x → Y' .z x
| f .s : (x : X .z) (x' : X' .z x) → VHom⁽ᵈ⁾ X (X .s x) X' (sym (X' .s x x')) Y' (sym (Y' .s x (f .z x x'))) f
]


` Composition of semisimplicial maps.
def Hom.comp (X Y Z : SST) (f : Hom X Y) (g : Hom Y Z) : Hom X Z := [
| .z ↦ x ↦ g .z (f .z x)
| .s ↦ x ↦
  Hom.comp⁽ᵈ⁾
    X (X .s x)
    Y (Y .s (f .z x))
    Z (Z .s (g .z (f .z x)))
    f (f .s x)
    g (g .s (f .z x))
]

` Precompose a Hom⁽ᵈ⁾ with a vertically displayed map.
def Hom.vcompl
  (X Y : SST)
  (X' X'' : SST⁽ᵈ⁾ X) (Y' : SST⁽ᵈ⁾ Y)
  (f : VHom X X' X'')
  (g : Hom X Y) (g' : Hom⁽ᵈ⁾ X X'' Y Y' g)
  : Hom⁽ᵈ⁾ X X' Y Y' g :=
[
| .z ↦ x x' ↦
  g' .z x (f .z x x')
| .s ↦ x x' ↦
  sym (Hom.vcompl⁽ᵈ⁾
    X (X .s x)
    Y (Y .s (g .z x))
    X' (sym (X' .s x x'))
    X'' (sym (X'' .s x (f .z x x')))
    Y' (sym (Y' .s (g .z x) (g' .z x (f .z x x'))))
    f (f .s x x')
    g (g .s x)
    g' (sym (g' .s x (f .z x x'))))
]

` The type of sections of a displayed semisimplicial type.
def Sec (X : SST) (Y : SST⁽ᵈ⁾ X) : Type := codata [
| S .z : (x : X .z) → Y .z x
| S .s : (x : X .z) → Sec⁽ᵈ⁾ X (X .s x) Y (sym (Y .s x (S .z x))) S
]

` Trivially display a semisimplicial type over another SST.
def SST.const (X Y : SST) : SST⁽ᵈ⁾ X := [
| .z ↦ Gel (X .z) (x ↦ Y .z)
| .s ↦ x y ↦ sym (SST.const⁽ᵈ⁾ X (X .s x) Y (Y .s (y .ungel)))
]

` Pull back a displayed SST along a semisimplicial map.
def SST.pullback (X Y : SST) (f : Hom X Y) (Y' : SST⁽ᵈ⁾ Y) : SST⁽ᵈ⁾ X := [
| .z ↦ Gel (X .z) (x ↦ Y' .z (f .z x))
| .s ↦ x x' ↦
  sym (SST.pullback⁽ᵈ⁾ X (X .s x)
    Y (Y .s (f .z x))
    f (f .s x)
    Y' (sym (Y' .s (f .z x) (x' .ungel))))
]

` The terminal SST.
def SST.⊤ : SST := [
| .z ↦ ⊤
| .s ↦ _ ↦ SST.⊤⁽ᵈ⁾
]

` Universal property of the terminal SST.
def SST.bang (A : SST) : Hom A SST.⊤ := [
| .z ↦ _ ↦ ()
| .s ↦ a ↦ SST.bang⁽ᵈ⁾ A (A .s a)
]

` The initial SST.
def SST.⊥ : SST := [
| .z ↦ ⊥
| .s ↦ []
]

` The initial SST is also a displayed initial object.
def SST.¡ᵛ (A : SST) (A' : SST⁽ᵈ⁾ A) : VHom A (SST.const A SST.⊥) A' := [
| .z ↦ a ff ↦ absurd (A' .z a) (ff .ungel)
| .s ↦ a ff ↦
  absurd
    (VHom⁽ᵈ⁾ A (A .s a)
      (SST.const A SST.⊥) (SST.const⁽ᵈ⁾ A (A .s a) SST.⊥ (SST.⊥ .s (ff .ungel)))
      A' (sym (A' .s a (absurd (A' .z a) (ff .ungel))))
      (SST.¡ᵛ A A'))
    (ff .ungel)
]

` A non-vertical version of SST.¡ᵛ that lives over a map `f : Hom A B`.
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
| .s ↦ x ↦ SST.const (Disc X) SST.⊥
]

` Vertical map that re-indexes `SST.const (Disc X) (Disc Y)` into a `Gel` of `Y`
` over `X`.
def Disc.gel (X Y : Type)
  : VHom (Disc X) (SST.const (Disc X) (Disc Y)) (Disc⁽ᵈ⁾ X (Gel X (_ ↦ Y)))
  := [
| .z ↦ x y ↦ (ungel := y .ungel)
| .s ↦ x y ↦
  ` No good way to construct this out of SST.¡ᵛ⁽ᵈ⁾, must be done by hand with `absurd` calls.
  ?
]

` The 0th representable semisimplex.
def Δ₀ : SST := Disc ⊤

` Universal property of `Disc X`; when specialized to `X = ⊤`, this gives
` us a simple form of the yoneda lemma for the 0th representable.
def よ₀ (X : Type) (A : SST) (a : X → A .z) : Hom (Disc X) A := [
| .z ↦ x ↦ a x
| .s ↦ x ↦ SST.¡² (Disc X) A (よ₀ X A a) (A .s (a x))
]

` The SST of families over `X`.
def Fam (X : Type) : SST := [
| .z ↦ X → Type
| .s ↦ X' ↦ Fam⁽ᵈ⁾ X (Gel X X')
]


` The weighted join of semisimplicial types.
def Join (X : Type) (A : SST) (B : SST) : SST := [
| .z ↦
  ` Weight the zero simplicies of A by X.
  (X × A .z) ⊔ B .z
| .s ↦ [

  ` FIXME: This case is super fishy! We shouldn't be using Gel along ⊥ here:
  ` this leads to problems when we try to write the left inclusion.
  ` Moreover, taking `SST.const B (Disc X)` can potentially mess up the higher
  ` dimensional structure of `B`; it feels like we only want to weight the vertices here.
  | inl. xa ↦ Join⁽ᵈ⁾ X (Gel X (_ ↦ ⊥)) A (A .s (xa .snd)) B (SST.const B (Disc X))
  | inr. b ↦ Join⁽ᵈ⁾ X (Gel X (_ ↦ ⊥)) A (SST.const A SST.⊥) B (B .s b)
  ]
]

` Cones and cocones are defined via unweighted joins of a semisimplex with the point.
def Cone (A : SST) : SST := Join ⊤ Δ₀ A
def Cocone (A : SST) : SST := Join ⊤ A Δ₀

` Recursion principle for joins.
` To build a map out of `A ⋆ B` weighted by W, we need to give maps out of `A` and `B`,
` along with a map over `g` that builds 1-simplicies that agree with `f`.
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

` The left inclusion into the weighted join.
` FIXME: At the moment, this is broken; requires some deeper thought into how the join is implemented.
def Join.inl
  (X : Type)
  (A B : SST)
  (x : X)
  : Hom A (Join X A B)
  :=
[
| .z ↦ a ↦ inl. (x, a)
| .s ↦ a ↦ Join.inl⁽ᵈ⁾ X (Gel X (_ ↦ ⊥)) A (A .s a) B (SST.const B (Disc X)) x (ungel := ?)
]

` The right inclusion into the join.
def Join.inr
  (X : Type)
  (A B : SST)
  : Hom B (Join X A B)
  :=
[
| .z ↦ b ↦ inr. b
| .s ↦ b ↦ Join.inr⁽ᵈ⁾ X (Gel X (_ ↦ ⊥)) A (SST.const A SST.⊥) B (B .s b)
]

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

` Generalized representables.
def Δ (X : Type) : Nat → SST := [
| zero. ↦ Disc X
| suc. n ↦ Cone (Δ X n)
]


` The type of generalized n-dimensional boundaries in an SST `A`.
def ○ (n : Nat) (A : SST) : Type := match n [
| zero. ↦ ⊤
| suc. n ↦
  sig
    (pt : A .z
    , ∂a : ○ n A
    , a : ● n A ∂a
    , ∂a' : ○⁽ᵈ⁾ n (Nat.degen n) A (A .s pt) ∂a
    )
]

` The type of generalized n-dimensional boundary fillers in an SST `A`.
and ● (n : Nat) (A : SST) (○a : ○ n A) : Type := match n [
| zero. ↦ A .z
| suc. n ↦ ●⁽ᵈ⁾ n (Nat.degen n) A (A .s (○a .pt)) (○a .∂a) (○a .∂a') (○a .a)
]


` The type of (n+1, k) horns.
def Horn' (n k : Nat) (h : k ≤ suc. n) (A : SST) : Type := match n [
| zero. ↦ match k [
  | zero. ↦ A .z ` (1, 0) horn
  | suc. k ↦ match k [
    | zero. ↦ A .z ` (1, 1) horn
    | suc. _ ↦ ⊥ ` There are no (1, k+2) horns
    ]
  ]
| suc. n ↦ match k [
  | zero. ↦
      `(n+2, 0) horn
      sig
      (pt : A .z
      , ∂a : ○ (suc. n) A
      , ∂a' : ○⁽ᵈ⁾ (suc. n) (Nat.degen (suc. n)) A (A .s pt) ∂a
      )
  | suc. k ↦
    `(n+2, k+1) horn
    sig
      (pt : A .z
      , ∂a : ○ (suc. n) A
      , a : ● (suc. n) A ∂a
      , Λa : Horn'⁽ᵈ⁾ n (Nat.degen n) k (Nat.degen k) h (Nat.lte.degen k (suc. n) h) A (A .s pt) (Horn.restrict n k h A ∂a)
      )
  ]
]

` Restrict the boundary of an n-simplex to a horn.
and Horn.restrict
  (n k : Nat)
  (h : k ≤ suc. n)
  (A : SST)
  (○a : ○ (suc. n) A)
  : Horn' n k h A := match n [
| zero. ↦ match k [
  | zero. ↦
    ` (1, 0) horn
    ○a .pt
  | suc. k ↦ match k [
    | zero. ↦
      ` (1, 1) horn
      ○a .a
    | suc. _ ↦ h
    ]
  ]
| suc. n ↦ match k [
  | zero. ↦
    ` (n+2, 0) horn
    (○a .pt, ○a .∂a, ○a .∂a')
  | suc. k ↦
    ` (n+2, k+1) horn
    (○a .pt
    , ○a .∂a
    , ○a .a
    , Horn.restrict⁽ᵈ⁾ n (Nat.degen n) k (Nat.degen k) h (Nat.lte.degen k (suc. n) h) A (A .s (○a .pt)) (○a .∂a) (○a .∂a'))

  ]
]

` The type of (n, k) horns; this is mainly a notational convienence, as the (0, 0)
` horn is a somewhat dubious object.
def Horn (n k : Nat) (h : k ≤ n) (A : SST) : Type := match n [
| zero. ↦ ⊤ ` Somewhat arbitrary choice: what is the (0,0) horn?
| suc. n ↦ Horn' n k h A
]

` The type of opposite face filler data for a horn.
def Horn'.face (n k : Nat) (h : k ≤ suc. n) (A : SST) (Λ : Horn' n k h A) : Type :=
match n [
| zero. ↦ match k [
  | zero. ↦
    `(1, 0) horn
    A .z
  | suc. k ↦ match k [
    | zero. ↦
      `(1, 1) horn
      A .z
    | suc. _ ↦ ⊥
    ]
  ]
| suc. n ↦ match k [
  | zero. ↦
    ` (n+2, 0) horn
    ● (suc. n) A (Λ .∂a)
  | suc. k ↦
    ` (n+2, k+1) horn
    Horn'.face⁽ᵈ⁾
      n (Nat.degen n)
      k (Nat.degen k)
      h (Nat.lte.degen k (suc. n) h)
      A (A .s (Λ .pt))
      (Horn.restrict n k h A (Λ .∂a)) (Λ .Λa)
      (Horn.restrict_face n k h A (Λ .∂a))
  ]
]

and Horn.restrict_face
  (n k : Nat)
  (h : k ≤ suc. n)
  (A : SST)
  (○a : ○ (suc. n) A)
  : Horn'.face n k h A (Horn.restrict n k h A ○a) := ?

` Type of "Kan Structures" on an SST.
def Kan (A : SST) : Type := ?

` Tests:
axiom A : SST
axiom x : A .z
axiom y : A .z
axiom α : A .s x .z y
axiom z : A .z
axiom β : A .s x .z z
axiom γ : A .s y .z z
axiom f : A .s x .s y α .z z β γ

def ○xy : ○ 1 A := (pt := x, ∂a := (), a := y, ∂a' := ())
def ●xy : ● 1 A ○xy := α

def ○yz : ○ 1 A := (pt := y, ∂a := (), a := z, ∂a' := ())
def ●yz : ● 1 A ○yz := γ

def ○αβ : ○⁽ᵈ⁾ 1 1 A (A .s x) ○yz := (pt := α, ∂a := (), a:= β, ∂a' := ())
def ●αβ : ●⁽ᵈ⁾ 1 1 A (A .s x) ○yz ○αβ ●yz := f

def ○αβγ : ○ 2 A := (pt := x, ∂a := ○yz, a := ●yz, ∂a' := ○αβ)
def ●αβγ : ● 2 A ○αβγ := ●αβ

` Inline definition of all of the above data. Note the ordering!
def ○αβγ' : ○ 2 A := (x, (y, (), z, ()), γ, (α, (), β, ()))
def ●αβγ' : ● 2 A ○αβγ := f

def Λ₁₋₀ : Horn 1 0 () A := x
def Λ₁₋₁ : Horn 1 1 () A := y

def Λ₂₋₀ : Horn 2 0 () A := (x, (y, (), z, ()), (α, (), β, ()))
def Λ₂₋₁ : Horn 2 1 () A := (x, (y, (), z, ()), γ, α)
def Λ₂₋₂ : Horn 2 2 () A := (x, (y, (), z, ()), γ, β)

def 𝟚₀ : Δ ⊤ 1 .z := inl. ((), ())
def 𝟚₁ : Δ ⊤ 1 .z := inr. ()
def 𝟚₀₁ : Δ ⊤ 1 .s 𝟚₀ .z 𝟚₁ := inr. (ungel := ())


def 𝟛₀ : Δ ⊤ 2 .z := inl. ((), ())
def 𝟛₁ : Δ ⊤ 2 .z := inr. 𝟚₀
def 𝟛₂ : Δ ⊤ 2 .z := inr. 𝟚₁
def 𝟛₀₁ : Δ ⊤ 2 .s 𝟛₀ .z 𝟛₁ := inr. (ungel := ())
def 𝟛₁₂ : Δ ⊤ 2 .s 𝟛₁ .z 𝟛₂ := inr. (inr. (ungel := ()))
def 𝟛₀₂ : Δ ⊤ 2 .s 𝟛₀ .z 𝟛₂ := inr. (ungel := ())
def 𝟛₀₁₂ : Δ ⊤ 2 .s 𝟛₀ .s 𝟛₁ 𝟛₀₁ .z 𝟛₂ 𝟛₀₂ 𝟛₁₂ :=
  inr. ?


` Lesson learned:
` * Never, ever, ever use ⊤ when doing coinductive definitions.
