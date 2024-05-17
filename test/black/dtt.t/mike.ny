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
def Gel (A : Type) : (A → Type) → Type⁽ᵈ⁾ A := A' ↦ sig x ↦ (ungel : A' x)

def Gel.intro (A : Type) (A' : A → Type) (x : A) (x' : A' x) : Gel A A' x :=
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


def Disc (X : Type) : SST := [
| .z ↦ X
| .s ↦ x ↦ SST.const (Disc X) SST.⊥ `Disc⁽ᵈ⁾ X (Gel X (_ ↦ ⊥))
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

def Δ₀ : SST := Disc ⊤

def よ₀ (A : SST) (a : A .z) : Hom Δ₀ A := [
| .z ↦ _ ↦ a
| .s ↦ _ ↦ SST.¡² (Disc ⊤) A (よ₀ A a) (A .s a)
]

def Join (X : Type) (A : SST) (B : SST) : SST := [
| .z ↦ (X × A .z) + B .z
| .s ↦ [
  | inl. xa ↦ Join⁽ᵈ⁾ X (Gel X (_ ↦ ⊥)) A (A .s (xa .snd)) B (SST.const B (Disc X))
  | inr. b ↦ Join⁽ᵈ⁾ X (Gel X (_ ↦ ⊥)) A (SST.const A SST.⊥) B (B .s b)
  ]
]

def Cone (A : SST) : SST := Join ⊤ Δ₀ A
def Cocone (A : SST) : SST := Join ⊤ A Δ₀

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

def Cone.rec
  (A B : SST)
  (f : Hom A B) (pt : B .z)
  (s : Hom⁽ᵈ⁾ A (SST.const A Δ₀) B (B .s pt) f)
  : Hom (Cone A) B
  := Join.rec ⊤ Δ₀ A B (よ₀ B pt) f (_ ↦ s)

def Cocone.rec
  (A B : SST)
  (f : Hom A B) (pt : B .z)
  (s : (a : A .z) → Hom⁽ᵈ⁾ Δ₀ (SST.const Δ₀ Δ₀) B (B .s (f .z a)) (よ₀ B pt))
  : Hom (Cocone A) B
  := Join.rec ⊤ A Δ₀ B f (よ₀ B pt) (a ↦ s (a .snd))

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


` Tests:
axiom A : SST
axiom x : A .z
axiom y : A .z
axiom α : A .s x .z y
axiom z : A .z
axiom β : A .s x .z z
axiom γ : A .s y .z z
axiom f : A .s x .s y α .z z β γ

def αᵒᵖ : SST.op A .s y .z x := (ungel := α)
def βᵒᵖ : SST.op A .s z .z x := (ungel := β)
def γᵒᵖ : SST.op A .s z .z y := (ungel := γ)

def fᵒᵖ : SST.op A .s z .s y γᵒᵖ .z x βᵒᵖ αᵒᵖ :=
  (ungel := sym ((ungel := f) : Gel⁽ᵈ⁾ (A .z) (A .s x .z) (b ↦ A .s b .z z) (y γ ↦ A .s x .s y γ .z z β) y α γᵒᵖ))
