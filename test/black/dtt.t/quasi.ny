def Gel (A : Type) (A' : A → Type) : Type⁽ᵈ⁾ A ≔ sig x ↦ (ungel : A' x)

def ASST : Type ≔ codata [
| X .z : Type
| X .s : ASST⁽ᵈ⁾ X
]

def Degen₀ (A : ASST) : ASST ≔ [
| .z ↦ (p : A .z) (x : A .s .z p) → A .s .s .z p x x
| .s ↦ Degen₀⁽ᵈ⁾ A (A .s)
]

def Degen₁ (A : ASST) : ASST⁽ᵈ⁾ (Degen₀ A) ≔ [
| .z ↦ Gel (Degen₀ A .z) (dp ↦ (p : A .z) (x y : A .s .z p) (α : A .s .s .z p x y) → A .s .s .s .z p x x (dp p x) y α α)
| .s ↦ sym (Degen₁⁽ᵈ⁾ A (A .s))
]

` Tests

axiom X : ASST
axiom p : X .z
axiom x : X .s .z p
axiom y : X .s .z p
axiom α : X .s .s .z p x y
axiom z : X .s .z p
axiom β : X .s .s .z p x z
axiom γ : X .s .s .z p y z
axiom f : X .s .s .s .z p x y α z β γ

axiom dp₀ : Degen₀ X .z
axiom dx₀  : Degen₀ X .s .z dp₀
axiom dy₀  : Degen₀ X .s .z dp₀
axiom dα₀  : Degen₀ X .s .s .z dp₀ dx₀ dy₀

axiom dp₁ : Degen₁ X .z dp₀
axiom dx₁ : Degen₁ X .s .z dp₀ dp₁ dx₀
axiom dy₁ : Degen₁ X .s .z dp₀ dp₁ dy₀

` 😎
echo dp₀ p x
echo dx₀ p x y α
echo dα₀ p x y α z β γ f

` 😵‍💫
echo dp₁ .ungel p x y α
dump dp₁
dump dp₁ .ungel
dump dx₁ .ungel
quit
