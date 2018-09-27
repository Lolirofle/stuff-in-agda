open import Logic.Classical.NaturalDeduction

module Logic.Classical.NaturalDeduction.Proofs {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} {Proof} ⦃ predicateEqTheory : PredicateEq.Theory{ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} (Proof) ⦄ where

open import Functional hiding (Domain)
open        Logic.Classical.NaturalDeduction.PredicateEq {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} (Proof) renaming (Theory to PredicateEqTheory)

open PredicateEqTheory (predicateEqTheory)

-- TODO: Move the ones which is constructive

[↔]-with-[∧]ₗ : ∀{a₁ a₂ b} → Proof(a₁ ⟷ a₂) → Proof((a₁ ∧ b) ⟷ (a₂ ∧ b))
[↔]-with-[∧]ₗ (proof) =
  ([↔]-intro
    (a₂b ↦ [∧]-intro (([↔]-elimₗ proof) ([∧]-elimₗ a₂b)) ([∧]-elimᵣ a₂b))
    (a₁b ↦ [∧]-intro (([↔]-elimᵣ proof) ([∧]-elimₗ a₁b)) ([∧]-elimᵣ a₁b))
  )

[↔]-with-[∧]ᵣ : ∀{a b₁ b₂} → Proof(b₁ ⟷ b₂) → Proof((a ∧ b₁) ⟷ (a ∧ b₂))
[↔]-with-[∧]ᵣ (proof) =
  ([↔]-intro
    (ab₂ ↦ [∧]-intro ([∧]-elimₗ ab₂) (([↔]-elimₗ proof) ([∧]-elimᵣ ab₂)))
    (ab₁ ↦ [∧]-intro ([∧]-elimₗ ab₁) (([↔]-elimᵣ proof) ([∧]-elimᵣ ab₁)))
  )

[↔]-with-[∧] : ∀{a₁ a₂ b₁ b₂} → Proof(a₁ ⟷ a₂) → Proof(b₁ ⟷ b₂) → Proof((a₁ ∧ b₁) ⟷ (a₂ ∧ b₂))
[↔]-with-[∧] (a₁a₂) (b₁b₂) =
  ([↔]-intro
    (a₂b₂ ↦ [∧]-intro (([↔]-elimₗ a₁a₂) ([∧]-elimₗ a₂b₂)) (([↔]-elimₗ b₁b₂) ([∧]-elimᵣ a₂b₂)))
    (a₁b₁ ↦ [∧]-intro (([↔]-elimᵣ a₁a₂) ([∧]-elimₗ a₁b₁)) (([↔]-elimᵣ b₁b₂) ([∧]-elimᵣ a₁b₁)))
  )

[↔]-with-[∨]ₗ : ∀{a₁ a₂ b} → Proof(a₁ ⟷ a₂) → Proof((a₁ ∨ b) ⟷ (a₂ ∨ b))
[↔]-with-[∨]ₗ (proof) =
  ([↔]-intro
    ([∨]-elim([∨]-introₗ ∘ ([↔]-elimₗ proof)) [∨]-introᵣ)
    ([∨]-elim([∨]-introₗ ∘ ([↔]-elimᵣ proof)) [∨]-introᵣ)
  )

[↔]-with-[∨]ᵣ : ∀{a b₁ b₂} → Proof(b₁ ⟷ b₂) → Proof((a ∨ b₁) ⟷ (a ∨ b₂))
[↔]-with-[∨]ᵣ (proof) =
  ([↔]-intro
    ([∨]-elim [∨]-introₗ ([∨]-introᵣ ∘ ([↔]-elimₗ proof)))
    ([∨]-elim [∨]-introₗ ([∨]-introᵣ ∘ ([↔]-elimᵣ proof)))
  )

[↔]-with-[∨] : ∀{a₁ a₂ b₁ b₂} → Proof(a₁ ⟷ a₂) → Proof(b₁ ⟷ b₂) → Proof((a₁ ∨ b₁) ⟷ (a₂ ∨ b₂))
[↔]-with-[∨] (a₁a₂) (b₁b₂) =
  ([↔]-intro
    ([∨]-elim ([∨]-introₗ ∘ ([↔]-elimₗ a₁a₂)) ([∨]-introᵣ ∘ ([↔]-elimₗ b₁b₂)))
    ([∨]-elim ([∨]-introₗ ∘ ([↔]-elimᵣ a₁a₂)) ([∨]-introᵣ ∘ ([↔]-elimᵣ b₁b₂)))
  )

[↔]-with-[∀] : ∀{f g} → (∀{x} → Proof(f(x) ⟷ g(x))) → Proof((∀ₗ f) ⟷ (∀ₗ g))
[↔]-with-[∀] (proof) =
  ([↔]-intro
    (allg ↦ [∀]-intro(\{x} → [↔]-elimₗ (proof{x}) ([∀]-elim(allg){x})))
    (allf ↦ [∀]-intro(\{x} → [↔]-elimᵣ (proof{x}) ([∀]-elim(allf){x})))
  )

[↔]-with-[∃] : ∀{f g} → (∀{x} → Proof(f(x) ⟷ g(x))) → Proof((∃ₗ f) ⟷ (∃ₗ g))
[↔]-with-[∃] (proof) =
  ([↔]-intro
    ([∃]-elim(\{x} → gx ↦ [∃]-intro{_}{x}([↔]-elimₗ (proof{x}) (gx))))
    ([∃]-elim(\{x} → fx ↦ [∃]-intro{_}{x}([↔]-elimᵣ (proof{x}) (fx))))
  )

postulate [∨][∧]-distributivityₗ : ∀{a b c} → Proof((a ∨ (b ∧ c)) ⟷ (a ∨ b)∧(a ∨ c))
postulate [∨][∧]-distributivityᵣ : ∀{a b c} → Proof(((a ∧ b) ∨ c) ⟷ (a ∨ c)∧(b ∨ c))
postulate [∧][∨]-distributivityₗ : ∀{a b c} → Proof((a ∧ (b ∨ c)) ⟷ (a ∧ b)∨(a ∧ c))
postulate [∧][∨]-distributivityᵣ : ∀{a b c} → Proof(((a ∨ b) ∧ c) ⟷ (a ∧ c)∨(b ∧ c))
postulate [≡]-substitute-this-is-almost-trivial : ∀{φ : Domain → Stmt}{a b} → Proof(((a ≡ b) ∧ φ(a)) ⟷ φ(b))
