def Gel (A : Type) (A' : A → Type) : Type⁽ᵈ⁾ A ≔ sig x ↦ (ungel : A' x)

def ASST : Type ≔ codata [
| X .z : Type
| X .s : ASST⁽ᵈ⁾ X
]

{` 0-Degeneracies `}
def Degen₀ (A : ASST) : ASST ≔ [
| .z ↦ (p : A .z) (x : A .s .z p) → A .s .s .z p x x
| .s ↦ Degen₀⁽ᵈ⁾ A (A .s)
]

{` 1-Degeneracies, displayed over 0-degeneracies. `}
def Degen₁ (A : ASST) : ASST⁽ᵈ⁾ (Degen₀ A) ≔ [
| .z ↦ Gel (Degen₀ A .z) (dp ↦ (p : A .z) (x y : A .s .z p) (α : A .s .s .z p x y) → A .s .s .s .z p x x (dp p x) y α α)
| .s ↦ sym (Degen₁⁽ᵈ⁾ A (A .s))
]

` Tests

` Set up a bunch of data in an augmented semisimplicial type.
axiom X : ASST
axiom p : X .z
axiom x : X .s .z p
axiom y : X .s .z p
axiom α : X .s .s .z p x y
axiom z : X .s .z p
axiom β : X .s .s .z p x z
axiom γ : X .s .s .z p y z
axiom f : X .s .s .s .z p x y α z β γ

` Likewise, define a handful of 0-degeneracies.
axiom dp₀ : Degen₀ X .z
axiom dx₀  : Degen₀ X .s .z dp₀
axiom dy₀  : Degen₀ X .s .z dp₀
axiom dα₀  : Degen₀ X .s .s .z dp₀ dx₀ dy₀

` Finally, define a handful of 1-degeneracies over our previous 0-degeneracies.
axiom dp₁ : Degen₁ X .z dp₀
axiom dx₁ : Degen₁ X .s .z dp₀ dp₁ dx₀
axiom dy₁ : Degen₁ X .s .z dp₀ dp₁ dy₀

` 😎 Printing out 0-degeneracies gives the expected types!
echo dp₀ p x
echo dx₀ p x y α
echo dα₀ p x y α z β γ f

` 😵‍💫 Printing out dp₁ works just fine, but attempting to work with dx₁ runs into trouble!
echo dp₁ .ungel p x y α

` We can debug print dx₁, and it seems like we should be able to `ungel` it. Moreover, it looks
` very much like the representation of dp₁.
dump dp₁
dump dx₁
{`
Output:
Act (Const dp₁, ) : Inst (Act (App (Act (App (Act (Const Gel, ), ?), ), ?), 1), ?)
Act (Const dx₁, ) : Inst (Act (App (Act (App (Act (Const Gel, d), ?), 1), ?), 21), ?)
`}

` We can also compare `dp₁` to `dp₁ .ungel`
dump dp₁ .ungel
{`
Output:
Act (Field (Act (Const dp₁, ), ungel), ) : Pi (?, ?, ?)
`}

` However, this complains!
dump dx₁ .ungel
{`
Output:
 ￫ error[E0800]
 record type with a nonidentity degeneracy applied is no longer a record, hence has no field named ungel
`}
