module Numeral.Natural.Prime.Proofs.FromDividesProduct where

open import Data
open import Functional
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs.Multiplication
open import Numeral.Natural.Prime
open import Numeral.Natural.Prime.Decidable
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Order
open import Relator.Equals
open import Structure.Relator.Properties
open import Syntax.Implication
open import Syntax.Type

-- Note: For the converse of this, see Numeral.Natural.Relation.Divisibility.Proofs.Productᵣ.coprime-divides-of-[⋅]
divides-of-[⋅]-is-prime : ∀{p} → (p ≥ 2) → (∀{x y} → (p ∣ (x ⋅ y)) → ((p ∣ x) ∨ (p ∣ y))) → Prime(p)
divides-of-[⋅]-is-prime {p} (succ(succ _)) prod =
  • Prime(p) ∨ Composite(p) :-[ prime-or-composite ]
  • (\{(intro A B) → let a = A + 2 ; b = B + 2 in
    reflexivity(_∣_) {a ⋅ b} ⇒
    (a ⋅ b) ∣ (a ⋅ b)             ⇒-[ prod{a}{b} ]
    ((a ⋅ b) ∣ a) ∨ ((a ⋅ b) ∣ b) ⇒-[ [∨]-elim
      ((\()) ∘ [⋅]-cancellationₗ {a} {1}{b} ∘ antisymmetry(_∣_)(_≡_) (divides-with-[⋅] {a}{a}{b} ([∨]-introₗ (reflexivity(_∣_)))))
      ((\()) ∘ [⋅]-cancellationᵣ {b} {1}{a} ∘ antisymmetry(_∣_)(_≡_) (divides-with-[⋅] {b}{a}{b} ([∨]-introᵣ (reflexivity(_∣_)))))
    ]
    ⊥ ⇒-end
  })
  ⇒₂-[ [∨]-not-right ]
  Prime(p) ⇒-end
