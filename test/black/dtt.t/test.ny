def Foo : Type := sig (A : Type)

axiom X : Type
axiom foo : Foo
axiom lunch : Foo⁽ᵈ⁾ foo
axiom dinner : Foo⁽ᵈᵈ⁾ foo lunch lunch

echo (sym dinner) .A

