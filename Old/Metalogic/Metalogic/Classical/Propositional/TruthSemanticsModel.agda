module Metalogic.Classical.Propositional.TruthSemanticsModel {ℓ} (Proposition : Set(ℓ)) where

import      Lvl
open import Data.Boolean
open import Data
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Metalogic.Classical.Propositional.Syntax{ℓ} (Proposition)
  renaming (
    ⊤   to ⊤ₗ ;
    ⊥   to ⊥ₗ ;
    ¬_  to ¬ₗ_ ;
    _∧_ to _∧ₗ_ ;
    _∨_ to _∨ₗ_ ;
    _⇒_ to _⇒ₗ_ )
open import Relator.Equals
open import Relator.Equals.Proofs
open import Sets.BoolSet

-- A model decides whether a proposition is true or false
-- Also known as Interpretation, Structure, Model
record Model : Set(ℓ) where
  field
    interpretProp : Proposition → Bool

-- TODO: Can this be called a "theory" of propositional logic? So that instances of the type Semantics is the "models" of logic?
-- TODO: Now, all the metalogic depends on booleans, which may not be satisfactory
module _ where
  import      Data.Boolean.Operators
  open        Data.Boolean.Operators.Logic

  satisfaction : Model → Formula → Bool
  satisfaction(𝔐)(• prop) = Model.interpretProp(𝔐) (prop)
  satisfaction(𝔐)(⊤ₗ) = 𝑇
  satisfaction(𝔐)(⊥ₗ) = 𝐹
  satisfaction(𝔐)(¬ₗ φ) = ¬(satisfaction(𝔐)(φ))
  satisfaction(𝔐)(φ₁ ∧ₗ φ₂) = (satisfaction(𝔐)(φ₁)) ∧ (satisfaction(𝔐)(φ₂))
  satisfaction(𝔐)(φ₁ ∨ₗ φ₂) = (satisfaction(𝔐)(φ₁)) ∨ (satisfaction(𝔐)(φ₂))
  satisfaction(𝔐)(φ₁ ⇒ₗ φ₂) = ¬(satisfaction(𝔐)(φ₁)) ∨ (satisfaction(𝔐)(φ₂))

  -- Syntactic details with the relation symbol
  record SatisfactionRelation {ℓ₁}{ℓ₂} (Obj : Set(ℓ) → Set(ℓ₁)) : Set(Lvl.𝐒(ℓ Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂)) where
    field
      _⊧_ : Model → Obj(Formula) → Set(ℓ₂)
  open SatisfactionRelation ⦃ ... ⦄ public

  instance
    -- Satisfaction for a single formula
    formula-satisfaction-relation : SatisfactionRelation(id)
    formula-satisfaction-relation = record{_⊧_ = \𝔐 φ → satisfaction(𝔐)(φ) ≡ 𝑇}

  instance
    -- Satisfaction for a list of formulas
    list-satisfaction-relation : SatisfactionRelation(BoolSet{ℓ})
    list-satisfaction-relation = record{_⊧_ = \𝔐 Γ → (∀{γ} → (γ ∈ Γ) → satisfaction(𝔐)(γ) ≡ 𝑇)}

  -- Entailment
  data _⊨_ (Γ : BoolSet{ℓ}(Formula)) (φ : Formula) : Set(ℓ) where
    [⊨]-intro : (∀{𝔐} → (𝔐 ⊧ Γ) → (𝔐 ⊧ φ)) → (Γ ⊨ φ)

  _⊭_ : BoolSet{ℓ}(Formula) → Formula → Set(ℓ)
  _⊭_ Γ φ = (_⊨_ Γ φ) → Empty{ℓ}

  -- Validity
  valid : Formula → Set(ℓ)
  valid = (∅ ⊨_)

  module Theorems where
    [⊤]-entailment : (∅ ⊨ ⊤ₗ)
    [⊤]-entailment = [⊨]-intro(const [≡]-intro)
    -- ∅ ⊨ ⊤ₗ
    -- ∀{𝔐} → (𝔐 ⊧ ∅) → (𝔐 ⊧ ⊤ₗ)
    -- ∀{𝔐} → (𝔐 ⊧ ∅) → (satisfaction(𝔐)(⊤ₗ) ≡ 𝑇)
    -- ∀{𝔐} → (∀{γ} → (γ ∈ ∅) → satisfaction(𝔐)(γ) ≡ 𝑇) → (satisfaction(𝔐)(⊤ₗ) ≡ 𝑇)

    -- [∧]-entailment : ∀{φ₁ φ₂} → ([ φ₁ ⊰ φ₂ ] ⊨ (φ₁ ∧ₗ φ₂))
    -- [∧]-entailment{φ₁}{φ₂} = [⊨]-intro ([∈]-proof ↦ [≡]-with-op(_∧_) ([∈]-proof ([∈]-use)) ([∈]-proof ([∈]-skip [∈]-use)))
    -- [ φ₁ ⊰ φ₂ ] ⊨ (φ₁ ∧ φ₂)
    -- ∀{𝔐} → (𝔐 ⊧ [ φ₁ ⊰ φ₂ ]) → (𝔐 ⊧ (φ₁ ∧ φ₂))
    -- ∀{𝔐} → (𝔐 ⊧ [ φ₁ ⊰ φ₂ ]) → (satisfaction(𝔐)(φ₁ ∧ₗ φ₂) ≡ 𝑇)
    -- ∀{𝔐} → (𝔐 ⊧ [ φ₁ ⊰ φ₂ ]) → (satisfaction(𝔐)(φ₁) ∧ satisfaction(𝔐)(φ₂) ≡ 𝑇)
    -- ∀{𝔐} → (∀{γ} → (γ ∈ [ φ₁ ⊰ φ₂ ]) → satisfaction(𝔐)(γ) ≡ 𝑇) → (satisfaction(𝔐)(φ₁) ∧ satisfaction(𝔐)(φ₂) ≡ 𝑇)
