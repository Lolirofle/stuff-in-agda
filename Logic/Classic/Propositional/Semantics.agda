module Logic.Classic.Propositional.Semantics {ℓ} (Prop : Set(ℓ)) where

import      Level as Lvl
open import Boolean
open import Functional
open import List
import      List.Theorems
open        List.Theorems.Sets{ℓ}{ℓ}
open import Logic.Classic.Propositional.Syntax{ℓ}(Prop)
open import Relator.Equals{ℓ}{ℓ}

-- A model decides whether a proposition is true or false
-- Also known as Interpretation, Structure, Model
record Model : Set(ℓ) where
  field
    interpretProp : Prop → Bool

-- TODO: Can this be called a "theory" of propositional logic? So that instances of the type Semantics is the "models" of logic?
module _ {MetaProp : Set(ℓ)} (_satisfies_ : Model → Prop → MetaProp) where
  open import Logic.Classic.Propositional.Syntax{ℓ}(MetaProp)
    renaming (
      Formula to Formulaₘ ;
      •_ to ◦_ ;
      ⊤   to ⊤ₘ ;
      ⊥   to ⊥ₘ ;
      ¬_  to ¬ₘ_ ;
      _∧_ to _∧ₘ_ ;
      _∨_ to _∨ₘ_ ;
      _⇒_ to _⇒ₘ_ )

{--
  satisfaction : Model → Formula → Formulaₘ
  satisfaction(𝔐)(• prop) = ◦(𝔐 satisfies prop)
  satisfaction(𝔐)(⊤) = ⊤ₘ
  satisfaction(𝔐)(⊥) = ⊥ₘ
  satisfaction(𝔐)(¬ φ) = ¬ₘ(satisfaction(𝔐)(φ))
  satisfaction(𝔐)(φ₁ ∧ φ₂) = (satisfaction(𝔐)(φ₁)) ∧ₘ (satisfaction(𝔐)(φ₂))
  satisfaction(𝔐)(φ₁ ∨ φ₂) = (satisfaction(𝔐)(φ₁)) ∨ₘ (satisfaction(𝔐)(φ₂))
  satisfaction(𝔐)(φ₁ ⇒ φ₂) = ¬ₘ(satisfaction(𝔐)(φ₁)) ∨ₘ (satisfaction(𝔐)(φ₂))

  -- Syntactic details with the relation symbol
  record SatisfactionRelation (T : Set(ℓ) → Set(ℓ)) : Set(Lvl.𝐒(ℓ)) where
    field
      _⊧_ : Model → T(Formula) → Formulaₘ
  open SatisfactionRelation{{...}} public

  instance
    -- Satisfaction for a single formula
    formula-satisfaction-relation : SatisfactionRelation(id)
    formula-satisfaction-relation = record{_⊧_ = \𝔐 φ → satisfaction(𝔐)(φ)}

  instance
    -- Satisfaction for a list of formulas
    list-satisfaction-relation : SatisfactionRelation(List)
    list-satisfaction-relation = record{_⊧_ = \𝔐 Γ → (∀{γ} → (γ ∈ Γ) → satisfaction(𝔐)(γ))}

  -- Entailment
  data _⊨_ (Γ : List(Formula)) (φ : Formula) : Set(ℓ) where
    [⊨]-construct : (∀{𝔐} → (𝔐 ⊧ Γ) → (𝔐 ⊧ φ)) → (Γ ⊨ φ)

  test : Model → MetaProp
  test(𝔐) = 𝔐 satisfies ⊥


  [⊨]-elim : ∀{Γ}{φ} → (Γ ⊨ φ) → Set(ℓ₁ Lvl.⊔ ℓ₂)
  [⊨]-elim {∅}     {φ} ([⊨]-construct proof) = ∀{𝔐 : Model(Prop)} → ◦(𝔐 ⊧ φ)
  [⊨]-elim {γ ⊰ Γ} {φ} ([⊨]-construct proof) = ∀{𝔐 : Model(Prop)} → (foldᵣ-init (_⨯_) (◦(𝔐 ⊧ γ)) (map (γ ↦ ◦(𝔐 ⊧ γ)) Γ)) → ◦(𝔐 ⊧ φ)

  _⊭_ : List(Formula(Prop)) → Formula(Prop) → Set(ℓ₁ Lvl.⊔ ℓ₂)
  _⊭_ Γ φ = ¬ₘ(_⊨_ Γ φ)

  -- Validity
  valid : Formula(Prop) → Set(ℓ₁ Lvl.⊔ ℓ₂)
  valid = (∅ ⊨_)

  module Theorems where
    [⊤]-entailment : (∅ ⊨ ⊤)
    [⊤]-entailment = [⊨]-construct(const [⊤]-satisfaction)

    [∧]-entailment : ∀{φ₁ φ₂} → ([ φ₁ ⊰ φ₂ ] ⊨ (φ₁ ∧ φ₂))
    [∧]-entailment {φ₁}{φ₂} = [⊨]-construct(f) where
      f : ∀{𝔐} → ◦(∀{γ} → (γ ∈ [ φ₁ ⊰ φ₂ ]) → ◦(𝔐 ⊧ γ)) → ◦(𝔐 ⊧ (φ₁ ∧ φ₂))
      f input = input φ₁[⊤]-satisfaction
      -- [ φ₁ ⊰ φ₂ ] ⊨ (φ₁ ∧ φ₂)
      -- ∀{𝔐} → ◦(𝔐 ⊧ [ φ₁ ⊰ φ₂ ]) → ◦(𝔐 ⊧ (φ₁ ∧ φ₂))
      -- ∀{𝔐} → ◦(∀{γ} → (γ ∈ [ φ₁ ⊰ φ₂ ]) → ◦(𝔐 ⊧ γ)) → ◦(𝔐 ⊧ (φ₁ ∧ φ₂))
    -- TODO: Try to prove some theorems with non-empty assumptions
--}
