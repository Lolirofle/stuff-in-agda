open import Formalization.PredicateLogic.Signature

module Formalization.PredicateLogic.Classical.SequentCalculus (𝔏 : Signature) where
open Signature(𝔏)

open import Data.List
open import Data.List.Functions using () renaming (singleton to · ; _++_ to _∪_)
open import Data.List.Relation.Permutation
open import Formalization.PredicateLogic.Syntax(𝔏)
open import Formalization.PredicateLogic.Syntax.Substitution(𝔏)
open import Functional as Fn
import      Lvl
open import Numeral.Finite
open import Numeral.Natural
open import Type

private variable ℓ : Lvl.Level
private variable n vars : ℕ

_∪·_ : ∀{T : Type{ℓ}} → List(T) → T → List(T)
_∪·_ = Fn.swap(_⊰_)
infixl 1000 _∪·_

module _ where
  private variable Γ Γ₁ Γ₂ Γ₃ Δ Δ₁ Δ₂ Δ₃ : List(Formula(vars))
  private variable φ φ₁ φ₂ ψ A B C : Formula(vars)
  private variable p : Prop(n)

  data _⇒_ : List(Formula(vars)) → List(Formula(vars)) → Type{Lvl.𝐒(ℓₚ Lvl.⊔ ℓₒ)} where
    axiom : ((· φ) ⇒ (· φ))

    weakenₗ : (Γ ⇒ Δ) → ((Γ ∪· A) ⇒ Δ)
    permuteₗ : .(Γ₁ permutes Γ₂) → (Γ₁ ⇒ Δ) → (Γ₂ ⇒ Δ)
    contractₗ : ((Γ ∪· A ∪· A) ⇒ Δ) → ((Γ ∪· A) ⇒ Δ)
    ⊥ₗ : (Γ ∪· ⊥) ⇒ ∅
    ∧ₗₗ : ((Γ ∪· A) ⇒ Δ) → ((Γ ∪· (A ∧ B)) ⇒ Δ)
    ∧ₗᵣ : ((Γ ∪· B) ⇒ Δ) → ((Γ ∪· (A ∧ B)) ⇒ Δ)
    ∨ₗ : ((Γ ∪· A) ⇒ Δ) → ((Γ ∪· B) ⇒ Δ) → ((Γ ∪· (A ∨ B)) ⇒ Δ)
    ⟶ₗ : (Γ ⇒ (Δ ∪· A)) → ((Γ ∪· B) ⇒ Δ) → ((Γ ∪· (A ⟶ B)) ⇒ Δ)
    Ɐₗ : ∀{t} → ((Γ ∪· (substitute0 t A)) ⇒ Δ) → ((Γ ∪· (Ɐ A)) ⇒ Δ)
    ∃ₗ : ∀{v}{n} → ((Γ ∪· (substituteN n (var v) A)) ⇒ Δ) → ((Γ ∪· (∃ A)) ⇒ Δ)

    weakenᵣ : (Γ ⇒ Δ) → (Γ ⇒ (Δ ∪· A))
    permuteᵣ : .(Δ₁ permutes Δ₂) → (Γ ⇒ Δ₁) → (Γ ⇒ Δ₂)
    contractᵣ : (Γ ⇒ (Δ ∪· A ∪· A)) → (Γ ⇒ (Δ ∪· A))
    ⊤ᵣ : ∅ ⇒ (Δ ∪· ⊤)
    ∧ᵣ : (Γ ⇒ (Δ ∪· A)) → (Γ ⇒ (Δ ∪· B)) → (Γ ⇒ (Δ ∪· (A ∧ B)))
    ∨ᵣₗ : (Γ ⇒ (Δ ∪· A)) → (Γ ⇒ (Δ ∪· (A ∨ B)))
    ∨ᵣᵣ : (Γ ⇒ (Δ ∪· B)) → (Γ ⇒ (Δ ∪· (A ∨ B)))
    ⟶ᵣ : ((Γ ∪· A) ⇒ (Δ ∪· B)) → (Γ ⇒ (Δ ∪· (A ⟶ B)))
    Ɐᵣ : ∀{v}{n} → (Γ ⇒ (Δ ∪· (substituteN n (var v) A))) → (Γ ⇒ (Δ ∪· (Ɐ A)))
    ∃ᵣ : ∀{t} → (Γ ⇒ (Δ ∪· (substitute0 t A))) → (Γ ⇒ (Δ ∪· (∃ A)))
