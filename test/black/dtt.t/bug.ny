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

def SST : Type ≔ codata [
| X .z : Type
| X .s : (X .z) → SST⁽ᵈ⁾ X
]

def SST.const (X Y : SST) : SST⁽ᵈ⁾ X ≔ [
| .z ↦ sig _ ↦ ( ungel : Y .z )
| .s ↦ x y ↦ sym (SST.const⁽ᵈ⁾ X (X .s x) Y (Y .s (y .ungel)))
]

`Cones
def Cone (A : SST) : SST := [
| .z ↦ Maybe (A .z)
| .s ↦ [
  | none. ↦ SST.const (Cone A) A
  | some. a ↦ [
    | .z ↦ SGel (Maybe (A .z)) (Maybe.rec (A .z) Type ⊥ (b ↦ A .s a .z b))
    | .s ↦ b b' ↦ match b [
      | none. ↦
        absurd
          (SST⁽ᵈᵈ⁾ (Cone A) (Cone A .s (some. a)) (SST.const (Cone A) A))
          (b' .ungel)
      | some. b ↦
        Cone⁽ᵈᵈ⁾ A (A .s a) ? (A .s a .s b (b' .ungel))
      ]
    ]
  ]
]
