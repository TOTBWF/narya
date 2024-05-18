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

def Nat.add (n : Nat) (m : Nat) : Nat := match n [
| zero. ↦ m
| suc. n ↦ suc. (Nat.add n m)
]

notation 5 Nat.add : n "+" k := Nat.add n k

` Degenerate a Nat into a Nat⁽ᵈ⁾.
def Nat.degen (n : Nat) : Nat⁽ᵈ⁾ n := match n [
| zero. ↦ zero.
| suc. n ↦ suc. (Nat.degen n)
]

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

def Disc (X : Type) : SST := [
| .z ↦ X
| .s ↦ x ↦ Disc⁽ᵈ⁾ X (Gel X (_ ↦ ⊥))
]

def Disc₂ (A : SST) (X : A .z → Type) : SST⁽ᵈ⁾ A := [
| .z ↦ Gel (A .z) (a ↦ X a)
| .s ↦ a x ↦ sym (Disc₂⁽ᵈ⁾ A (A .s a) X (b α ↦ Gel (X b) (_ ↦ ⊥)))
]


` def Mike (X : Nat → Type) : Π⁽ᵈ⁾ Nat Nat⁽ᵈ⁾ (_ ↦ Type) (_ ⤇ Type⁽ᵈ⁾) X :=
`   i _ ↦ match i [
`   | zero. ↦ Gel (X 0) (_ ↦ ⊥)
`   | suc. i ↦ Gel (X (suc. i)) (_ ↦ X (suc. i))
`   ]

def ▲₀ : SST := Disc ⊤

def ▲ (X : Nat → Type) : Nat → SST := [
| zero. ↦ Disc (X 0)
| suc. n ↦ ▲⁺ X n
]

and ▲⁺ (X : Nat → Type) (n : Nat) : SST := [
| .z ↦ X 0 ⊔ ▲ (i ↦ X (suc. i)) n .z
| .s ↦ v ↦ ▲⁺⁽ᵈ⁾ X (Cool X n (▲.dim X (suc. n) v)) n (Nat.degen n)
]

and Cool
  (X : Nat → Type) (n k : Nat)
  : Π⁽ᵈ⁾ Nat Nat⁽ᵈ⁾ (_ ↦ Type) (_ ⤇ Type⁽ᵈ⁾) X
  :=
  i _ ↦ match i [
  | zero. ↦ Gel (X 0) (_ ↦ ⊥)
  | suc. i ↦ match k [
    | zero. ↦ Gel (X (suc. i)) (_ ↦ X (suc. i))
    | suc. k ↦ Cool (i ↦ X (suc. i)) n k i (Nat.degen i)
    ]
  ]

and ▲.dim (X : Nat → Type) (n : Nat) (v : ▲ X n .z) : Nat :=
match n [
| zero. ↦ zero.
| suc. n ↦ match v [
  | inl. _ ↦ 0
  | inr. v ↦ suc. (▲.dim (i ↦ X (suc. i)) n v)
  ]
]

def 𝟙₀ : ▲ (_ ↦ ⊤) 1 .z := inl. ()
def 𝟙₁ : ▲ (_ ↦ ⊤) 1 .z := inr. ()

` def 𝟙₀₀ : ▲ (_ ↦ ⊤) 1 .s 𝟙₀ .z 𝟙₀ := ?
def 𝟙₀₁ : ▲ (_ ↦ ⊤) 1 .s 𝟙₀ .z 𝟙₁ := inr. (ungel := ())
` def 𝟙₁₀ : ▲ (_ ↦ ⊤) 1 .s 𝟙₁ .z 𝟙₀ := ? `inr. (ungel := ())
` def 𝟙₁₁ : ▲ (_ ↦ ⊤) 1 .s 𝟙₁ .z 𝟙₁ := ? `inr. ()

def 𝟚₀ : ▲ (_ ↦ ⊤) 2 .z := inl. ()
def 𝟚₁ : ▲ (_ ↦ ⊤) 2 .z := inr. 𝟙₀
def 𝟚₂ : ▲ (_ ↦ ⊤) 2 .z := inr. 𝟙₁

def 𝟚₀₁ : ▲ (_ ↦ ⊤) 2 .s 𝟚₀ .z 𝟚₁ := inr. (inl. (ungel := ()))
def 𝟚₀₂ : ▲ (_ ↦ ⊤) 2 .s 𝟚₀ .z 𝟚₂ := inr. (inr. (ungel := ()))
def 𝟚₁₂ : ▲ (_ ↦ ⊤) 2 .s 𝟚₁ .z 𝟚₂ := inr. 𝟙₀₁

def 𝟚₀₁₂ : ▲ (_ ↦ ⊤) 2 .s 𝟚₀ .s 𝟚₁ 𝟚₀₁ .z 𝟚₂ 𝟚₀₂ 𝟚₁₂ := inr. (inr. (ungel := (ungel := ())))
