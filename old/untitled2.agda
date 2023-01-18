module _ {A : Type{ℓ}} ⦃ equiv-A : Equiv{ℓₑ}(A) ⦄ where
  classical-constant-endofunction-existence : ⦃ classical : Classical(A) ⦄ → ∃{Obj = A → A}(Constant)
  classical-constant-endofunction-existence with excluded-middle(A)
  ... | [∨]-introₗ a  = [∃]-intro (const a)
  ... | [∨]-introᵣ na = [∃]-intro id ⦃ intro(\{a} → [⊥]-elim(na a)) ⦄
