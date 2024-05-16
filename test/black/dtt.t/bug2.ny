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

def SGel.intro (A : Type) (A' : A → Type) (x : A) (x' : A' x) : SGel A A' x :=
  (ungel := x')

def SGel²
  (Ap : Type) (Ax Ay : Type⁽ᵈ⁾ Ap)
  (Aα : (p : Ap) → Ax p → Ay p → Type)
  : Type⁽ᵈᵈ⁾ Ap Ax Ay := sig p x y ↦ (ungel : Aα p x y)

def SST : Type ≔ codata [
| X .z : Type
| X .s : (X .z) → SST⁽ᵈ⁾ X
]

def Hom (X Y : SST) : Type ≔ codata [
| f .z : X .z → Y .z
| f .s : (x : X .z) → Hom⁽ᵈ⁾ X (X .s x) Y (Y .s (f .z x)) f
]

` def VHom (X : SST) (X' Y' : SST⁽ᵈ⁾ X) : Type := codata [
` | f .z : (x : X .z) → X' .z x → Y' .z x
` | f .s : (x : X .z) (x' : X' .z x) → VHom⁽ᵈ⁾ X (X .s x) X' (sym (X' .s x x')) Y' (sym (Y' .s x (f .z x x'))) f
` ]

` def SST.vpullbackr
`   (X : SST)
`   (X' Y' Z' : SST⁽ᵈ⁾ X)
`   (f : VHom X Y' Z')
`   (Z'' : SST⁽ᵈᵈ⁾ X X' Z')
`   : SST⁽ᵈᵈ⁾ X X' Y' :=
` [
` | .z ↦ ?
` | .s ↦ ?
` ]

def SST.const (X Y : SST) : SST⁽ᵈ⁾ X ≔ [
| .z ↦ SGel (X .z) (x ↦ Y .z) `sig _ ↦ ( ungel : Y .z )
| .s ↦ x y ↦ sym (SST.const⁽ᵈ⁾ X (X .s x) Y (Y .s (y .ungel)))
]

def SST.⊤ : SST ≔ [
| .z ↦ ⊤
| .s ↦ _ ↦ SST.⊤⁽ᵈ⁾
]


`Cones

def Cone (X : Type) (A : SST) : SST := [
| .z ↦ X + A .z
| .s ↦ [
  | inl. x ↦ Cone⁽ᵈ⁾ X (SGel X (_ ↦ ⊥)) A (SST.const A SST.⊤)
  | inr. a ↦ Cone⁽ᵈ⁾ X (SGel X (_ ↦ ⊥)) A (A .s a)
  ]
]

axiom A : SST
axiom x : A .z
axiom y : A .z
axiom α : A .s x .z y

def K : SST := Cone ⊤ A
def k∞ : K .z := inl. ()
def kx : K .z := inr. x
def ky : K .z := inr. y
def kα : K .s kx .z ky := inr. α

def k∞x : K .s k∞ .z kx := inr. (ungel := ())
def k∞y : K .s k∞ .z ky := inr. (ungel := ())

def k∞α : K .s k∞ .s kx k∞x .z ky k∞y kα :=
  inr. (sym (SGel.intro⁽ᵈ⁾ ? ? ? ? ? ? ? ?))
  `(sym (? : SST.const⁽ᵈ⁾ A (A .s x) SST.⊤ SST.⊤⁽ᵈ⁾ .z y α (ungel := ())))

