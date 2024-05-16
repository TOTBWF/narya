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

def Prod (A : Type) (B : Type) : Type :=
  sig (fst : A, snd : B)

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
notation 6 Prod : A "×" B := Prod A B

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

def SST : Type := codata [
| X .z : Type
| X .s : (X .z) → SST⁽ᵈ⁾ X
]

def Hom (X Y : SST) : Type := codata [
| f .z : X .z → Y .z
| f .s : (x : X .z) → Hom⁽ᵈ⁾ X (X .s x) Y (Y .s (f .z x)) f
]

def Sec (X : SST) (Y : SST⁽ᵈ⁾ X) : Type := codata [
| S .z : (x : X .z) → Y .z x
| S .s : (x : X .z) → Sec⁽ᵈ⁾ X (X .s x) Y (sym (Y .s x (S .z x))) S
]

def SST.const (X Y : SST) : SST⁽ᵈ⁾ X := [
| .z ↦ SGel (X .z) (x ↦ Y .z) `sig _ ↦ ( ungel : Y .z )
| .s ↦ x y ↦ sym (SST.const⁽ᵈ⁾ X (X .s x) Y (Y .s (y .ungel)))
]

def SST.pullback (X Y : SST) (f : Hom X Y) (Y' : SST⁽ᵈ⁾ Y) : SST⁽ᵈ⁾ X := [
| .z ↦ SGel (X .z) (x ↦ Y' .z (f .z x))
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



def Disc (X : Type) : SST := [
| .z ↦ X
| .s ↦ _ ↦ Disc⁽ᵈ⁾ X (SGel X (_ ↦ ⊥))
]

def SST.⊥ : SST := Disc ⊥

def Δ₀ : SST := Disc ⊤

def Join (X : Type) (A : SST) (B : SST) : SST := [
| .z ↦ (X × A .z) + B .z
| .s ↦ [
  | inl. xa ↦ Join⁽ᵈ⁾ X (SGel X (_ ↦ ⊥)) A (A .s (xa .snd)) B (SST.const B (Disc X))
  | inr. b ↦ Join⁽ᵈ⁾ X (SGel X (_ ↦ ⊥)) A (SST.const A SST.⊥) B (B .s b)
  ]
]

` Mike defn, with optimized SST.const case on inl.
def Cone (X : Type) (A : SST) : SST := [
| .z ↦ X + A .z
| .s ↦ [
  | inl. x ↦ Cone⁽ᵈ⁾ X (SGel X (_ ↦ ⊥)) A (SST.const A (Disc X))
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



`def Cone (X : Type) (A : SST) : SST := Join X (Disc X) A
` def Cocone (X : Type) (A : SST) : SST := Join X A (Disc X)


` def Disc.lift (X : Type) (A B : SST) (f : Hom A B) : Hom⁽ᵈ⁾ A (SST.const A (Disc X)) B (SST.const B (Disc X)) f :=
` [
` | .z ↦ a x ↦ (ungel := x .ungel)
` | .s ↦ a x ↦ sym (Disc.lift⁽ᵈ⁾ X (SGel X (_ ↦ ⊥)) A (A .s a) B (B .s (f .z a)) f (f .s a))
` ]


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
      X (SGel X (_ ↦ ⊥))
      A (A .s (xa .snd))
      B (SST.const B (Disc X))
      T (T .s (f .z (xa .snd)))
      f (f .s (xa .snd))
      g (s xa)
      s (xa' ff ↦ ?)
  | inr. b ↦
    Join.rec⁽ᵈ⁾
      X (SGel X (_ ↦ ⊥))
      A (SST.const A SST.⊥)
      B (B .s b)
      T (T .s (g .z b))
      f ?
      g (g .s b)
      s ?
  ]
]

` def Cone.rec
`   (X : Type) (A B : SST)
`   (f : Hom A B) (pt : X → B .z)
`   (s : (x : X) → Hom⁽ᵈ⁾ A (SST.const A (Disc X)) B (B .s (pt x)) f)
`   : Hom (Cone X A) B :=
` [
` | .z ↦ [
`   | inl. x ↦ pt x
`   | inr. a ↦ f .z a
`   ]
` | .s ↦ [
`   | inl. x ↦
`     Cone.rec⁽ᵈ⁾
`       X (SGel X (_ ↦ ⊥))
`       A (SST.const A (Disc X))
`       B (B .s (pt x))
`       f (s x)
`       pt (x' ff ↦ absurd (B .s (pt x) .z (pt x')) (ff .ungel))
`       ` lol, lmao, etc
`       s (x' ff ↦
`         absurd
`           (Hom⁽ᵈᵈ⁾ A
`             (SST.const A (Disc X))
`             (SST.const A (Disc X))
`             (SST.const⁽ᵈ⁾ A (SST.const A (Disc X)) (Disc X) (Disc⁽ᵈ⁾ X (SGel X (_ ↦ ⊥))))
`             B (B .s (pt x)) (B .s (pt x'))
`             (B .s (pt x) .s (pt x') (absurd (B .s (pt x) .z (pt x')) (ff .ungel))) f (s x) (s x'))
`             (ff .ungel))
`   | inr. a ↦
`     Cone.rec⁽ᵈ⁾
`       X (SGel X (_ ↦ ⊥))
`       A (A .s a)
`       B (B .s (f .z a))
`       f (f .s a)
`       pt (x ff ↦ absurd (B .s (f .z a) .z (pt x)) (ff .ungel))
`       s (x ff ↦ ?
`         ` absurd
`         `   ()
`         `   (ff .ungel)
`           )
`     ` Cone.rec⁽ᵈ⁾
`     `   A (A .s a)
`     `   X ? `(SST.const A SST.⊥)
`     `   f ?
`     `   pt ?
`   ]
` ]

` def Join.rec
`   (A B X : SST)
`   (f : Hom A X) (g : Hom B X)
`   `(s : (a : A .z) → Sec B (SST.pullback B X g (X .s (f .z a))))
`   : Hom (Join A B) X :=
` [
` | .z ↦ [
`   | inl. a ↦ f .z a
`   | inr. b ↦ g .z b
`   ]
` | .s ↦ [
`   | inl. a ↦
`     Join.rec⁽ᵈ⁾
`       A (A .s a)
`       B (SST.const B SST.⊤)
`       X (X .s (f .z a))
`       f (f .s a)
`       g ?
`       s ?`(a' α ↦ s a .s ?)
`       `((SST.pullback B X g (X .s (f .z a)))) `(X .s (f .z a))
`   | inr. b ↦
`     Join.rec⁽ᵈ⁾
`       A (SST.const A SST.⊥)
`       B (B .s b)
`       X (X .s (g .z b))
`       f ?
`       g (g .s b)
`       ? ?
`   ]
` ]
` axiom A : SST
` axiom x : A .z
` axiom y : A .z
` axiom α : A .s x .z y

` def K : SST := Cone ⊤ A
` def k∞ : K .z := inl. ()
` def kx : K .z := inr. x
` def ky : K .z := inr. y
` def kα : K .s kx .z ky := inr. α

` def k∞x : K .s k∞ .z kx := inr. (ungel := ())
` def k∞y : K .s k∞ .z ky := inr. (ungel := ())

` ` Obviously true, but annoying to provide arguments
` def k∞α : K .s k∞ .s kx k∞x .z ky k∞y kα :=
`   inr. (sym (SGel.intro⁽ᵈ⁾ ? ? ? ? ? ? ? ?))
`   `(sym (? : SST.const⁽ᵈ⁾ A (A .s x) SST.⊤ SST.⊤⁽ᵈ⁾ .z y α (ungel := ())))

