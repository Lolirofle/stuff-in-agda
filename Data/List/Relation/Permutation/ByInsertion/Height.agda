module Data.List.Relation.Permutation.ByInsertion.Height where

open import Data.List using (List ; _⊰_)
open import Data.List.Functions as List using (length ; insertIn)
open import Data.List.Relation.Permutation.ByInsertion
open import Data.List.Relation.Permutation.ByInsertion.Proofs
open import Logic.Propositional
import      Lvl
open import Numeral.Natural
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}
private variable l₁ l₂ : List(T)

height : (l₁ permutes l₂) → ℕ
height empty        = 𝟎
height (ins _ perm) = 𝐒(height perm)

height-is-lengthᵣ : ∀{perm : l₁ permutes l₂} → (height perm ≡ length l₂)
height-is-lengthᵣ {l₁ = _} {l₂ = _} {perm = empty}             = [≡]-intro
height-is-lengthᵣ {l₁ = l₁}{l₂ = l₂}{perm = ins{x = x} n perm} = congruence₁(𝐒) (height-is-lengthᵣ{perm = perm})

height-is-lengthₗ : ∀{perm : l₁ permutes l₂} → (height perm ≡ length l₁)
height-is-lengthₗ {perm = perm} = height-is-lengthᵣ 🝖 symmetry(_≡_) (permutes-preserves-length perm)

open import Data.Tuple
open import Logic.Predicate
open import Numeral.Natural.Relation
open import Syntax.Function

height-step : ∀{perm : l₁ permutes l₂} → Positive(height perm) → ∃{Obj = T ⨯ List(T) ⨯ List(T)}(\{(x , l1 , l2) → ∃(n ↦ (l₁ ≡ insertIn x l1 n) ∧ (l₂ ≡ x ⊰ l2) ∧ ∃{Obj = l1 permutes l2}(p ↦ height perm ≡ 𝐒(height(p))))})
height-step {perm = ins {l₁ = l₁} {l₂ = l₂} {x} n perm} pos = [∃]-intro (x , l₁ , l₂) ⦃ [∃]-intro n ⦃ [∧]-intro ([∧]-intro [≡]-intro [≡]-intro) ([∃]-intro perm ⦃ [≡]-intro ⦄) ⦄ ⦄

  {-
  open import Numeral.Natural.Relation.Order
  open import Numeral.Natural.Relation.Order.Proofs
  strong-elim : ∀{ℓ}(P : ∀{l₁ l₂ : List(T)} → (l₁ permutes l₂) → Type{ℓ}) → (∀{l₁ l₂ l₃ l₄}(perm₁ : l₁ permutes l₂)(perm₂ : l₃ permutes l₄) → (height perm₁ < height perm₂) → P(perm₁) → P(perm₂)) → (∀{l₁ l₂}(perm : l₁ permutes l₂) → P(perm))
  strong-elim P step perm = elim(\{l₃}{l₄} perm₂ → ∀{l₁ l₂}(perm₁ : l₁ permutes l₂) → (height perm₁ < height perm₂) → P(perm₂))
    (\_ ())
    (\{ {l₃}{l₄}{x}{n} perm₂ prev {l₁}{l₂} perm₁ (succ ph) → step {!!} {!!} {!!} {!!} })
    (ins{x = {!!}} 𝟎 perm)
    perm
    {!(reflexivity(_≤_))!}
  -}
