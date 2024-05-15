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

def coprod.rec (A B X : Type) (f : A → X) (g : B → X) : A + B → X := [
| inl. a ↦ f a
| inr. b ↦ g b
]


def Gel (A : Type) (A' : A → Type) : Type⁽ᵈ⁾ A ≔ sig x ↦ (ungel : A' x)
{` Simplices + Augmented Simplices `}

def SST : Type ≔ codata [
| X .z : Type
| X .s : (X .z) → SST⁽ᵈ⁾ X
]

def ASST : Type ≔ codata [
| X .z : Type
| X .s : ASST⁽ᵈ⁾ X
]

def SST.⊥ : SST ≔ [
| .z ↦ ⊥
| .s ↦ [ ]
]

def SST.⊤ : SST ≔ [
| .z ↦ ⊤
| .s ↦ _ ↦ SST.⊤⁽ᵈ⁾
]

def SST.const (X Y : SST) : SST⁽ᵈ⁾ X ≔ [
| .z ↦ sig _ ↦ ( ungel : Y .z )
| .s ↦ x y ↦ sym (SST.const⁽ᵈ⁾ X (X .s x) Y (Y .s (y .ungel)))
]

def Hom (X Y : SST) : Type ≔ codata [
| f .z : X .z → Y .z
| f .s : (x : X .z) → Hom⁽ᵈ⁾ X (X .s x) Y (Y .s (f .z x)) f
]

def Sec (X : SST) (Y : SST⁽ᵈ⁾ X) : Type := codata [
| S .z : (x : X .z) → Y .z x
| S .s : (x : X .z) → Sec⁽ᵈ⁾ X (X .s x) Y (sym (Y .s x (S .z x))) S
]

def SST.pullback (X Y : SST) (f : Hom X Y) (Y' : SST⁽ᵈ⁾ Y) : SST⁽ᵈ⁾ X := [
| .z ↦ Gel (X .z) (x ↦ Y' .z (f .z x))
| .s ↦ x x' ↦
  sym (SST.pullback⁽ᵈ⁾ X (X .s x)
    Y (Y .s (f .z x))
    f (f .s x)
    Y' (sym (Y' .s (f .z x) (x' .ungel))))
]

{` 0-Degeneracies `}
def Degen₀ (A : ASST) : ASST ≔ [
| .z ↦ (p : A .z) (x : A .s .z p) → A .s .s .z p x x
| .s ↦ Degen₀⁽ᵈ⁾ A (A .s)
]

{` 1-Degeneracies, displayed over 0-degeneracies. `}
def Degen₁ (A : ASST) : ASST⁽ᵈ⁾ (Degen₀ A) ≔ [
| .z ↦
  Gel (Degen₀ A .z)
    (dp ↦
      (p : A .z) (x y : A .s .z p) (α : A .s .s .z p x y) →
      A .s .s .s .z p x x (dp p x) y α α)
| .s ↦ sym (Degen₁⁽ᵈ⁾ A (A .s))
]

def Cone (A : SST) : SST := [
| .z ↦ Maybe (A .z)
| .s ↦ [
  | none. ↦ SST.const (Cone A) SST.⊥
  | some. a ↦ Cone⁽ᵈ⁾ A (A .s a)
  ]
]

` Extend a displayed SST over `A` to a displayed SST over `Cone A` by extending
` with empty fibres.
def Cone.extend (A : SST) (A' : SST⁽ᵈ⁾ A) : SST⁽ᵈ⁾ (Cone A) := [
| .z ↦ Gel (Maybe (A .z)) (Maybe.rec (A .z) Type ⊥ (a ↦ A' .z a))
| .s ↦ x x' ↦ match x [
  | none. ↦ absurd (SST⁽ᵈᵈ⁾ (Cone A) (Cone.extend A A') (SST.const (Cone A) SST.⊥)) (x' .ungel)
  | some. a ↦ sym (Cone.extend⁽ᵈ⁾ A (A .s a) A' (sym (A' .s a (x' .ungel))))
  ]
]

def Cone' (A : SST) : Maybe (A .z) → SST⁽ᵈ⁾ A := [
| none. ↦ SST.const A A
| some. a ↦ A .s a
]

def Glue (A : SST) (K : Maybe (A .z) → SST⁽ᵈ⁾ A) : SST := [
| .z ↦ Maybe (A .z)
| .s ↦ x ↦ ?
` [
`   | none. ↦ ?
`   | some. a ↦ ?
`   ]
]

` def Cool (A : SST) : SST := [
` | .z ↦ Maybe (A .z)
` | .s ↦ ?
` ]

` def Cone' (A : SST) : SST := [
` | .z ↦ Maybe (A .z)
` | .s ↦ [
`   | none. ↦ SST.const (Cone' A) A
`   | some. a ↦ [
`     | .z ↦ Gel (Maybe (A .z)) (Maybe.rec (A .z) Type ⊥ (b ↦ A .s a .z b))
`     | .s ↦ x x' ↦ match x [
`       | none. ↦
`         absurd (SST⁽ᵈᵈ⁾ (Cone' A) (Cone' A .s (some. a)) (SST.const (Cone' A) A)) (x' .ungel)
`       | some. b ↦
`         Cone'⁽ᵈᵈ⁾ A (A .s a) (A .s b) (A .s a .s b (x' .ungel))
`         ` have x' .ungel : A .s a .z b
`       ]
`     ]
`   ]
` ]

` and Cone'.extend (A : SST) (a : A .z) : SST⁽ᵈ⁾ (Cone' A) := [
` | .z ↦ Gel (Maybe (A .z)) (Maybe.rec (A .z) Type ⊥ (b ↦ A .s a .z b))
` | .s ↦ x x' ↦ match x [
`   | none. ↦ absurd (SST⁽ᵈᵈ⁾ (Cone' A) (Cone'.extend A a) (SST.const (Cone' A) A)) (x' .ungel)
`   | some. b ↦
`     ` have x' .ungel : A .s a .z b
`     Cone'.extend⁽ᵈ⁾ A (A .s a) b (x' .ungel)
`   ]
` ]


{`
We need to invert the cone somehow.

`}

def Cone.rec
  (X Y : SST)
  (pt : Y .z)
  (f : Hom X Y)
  (g : Sec X (SST.pullback X Y f (Y .s pt)))
  : Hom (Cone X) Y := [
  | .z ↦ [
    | none. ↦ pt
    | some. x ↦ f .z x
  ]
  | .s ↦ [
    | none. ↦ ?
    ` Cone.rec⁽ᵈ⁾ X (X .s ?) Y ? pt ? f ? g ?
    | some. x ↦ Cone.rec⁽ᵈ⁾ X (X .s x) Y (Y .s (f .z x)) pt (g .z x .ungel) f ? g ?
  ]
]

` ` NOTE: These really want to be augmented...
` def Δ : Nat → SST := [
` | zero. ↦ Cone SST.⊥
` | succ. n ↦ Cone (Δ n)
` ]

` Tests

` ` Set up a bunch of data in an augmented semisimplicial type.
` axiom X : ASST
` axiom p : X .z
` axiom x : X .s .z p
` axiom y : X .s .z p
` axiom α : X .s .s .z p x y
` axiom z : X .s .z p
` axiom β : X .s .s .z p x z
` axiom γ : X .s .s .z p y z
` axiom f : X .s .s .s .z p x y α z β γ

` ` Likewise, define a handful of 0-degeneracies.
` axiom dp₀ : Degen₀ X .z
` axiom dx₀  : Degen₀ X .s .z dp₀
` axiom dy₀  : Degen₀ X .s .z dp₀
` axiom dα₀  : Degen₀ X .s .s .z dp₀ dx₀ dy₀

` ` Finally, define a handful of 1-degeneracies over our previous 0-degeneracies.
` axiom dp₁ : Degen₁ X .z dp₀
` axiom dx₁ : Degen₁ X .s .z dp₀ dp₁ dx₀
` axiom dy₁ : Degen₁ X .s .z dp₀ dp₁ dy₀

` ` 😎 Printing out 0-degeneracies gives the expected types!
` echo dp₀ p x
` echo dx₀ p x y α
` echo dα₀ p x y α z β γ f

` ` 😵‍💫 Printing out dp₁ works just fine, but attempting to work with dx₁ runs into trouble!
` echo dp₁ .ungel p x y α
` echo (sym dx₁) .ungel p x y α z β γ f

axiom X : SST
axiom y : X .z
axiom z : X .z
axiom γ : X .s y .z z

def K : SST := Cone X

def kx : K .z := none.
def ky : K .z := some. y
def kz : K .z := some. z

` There are no 1-cells from (into?) an adjoined point `x`.
def bad (pt : K .z) (α : K .s kx .z pt) : ⊥ := α .ungel

def kα : K .s ky .z kx := none.
