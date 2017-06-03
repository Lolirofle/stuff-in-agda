module Logic.Classic.Propositional.Semantics {ℓ} (Prop : Set(ℓ)) where

import      Level as Lvl
open import Boolean
open import Data
open import Functional
open import List
import      List.Theorems
open        List.Theorems.Sets{ℓ}{ℓ}
open import Logic.Classic.Propositional.Syntax{ℓ} (Prop)
  renaming (
    Formula to Formulaₗ ;
    ⊤   to ⊤ₗ ;
    ⊥   to ⊥ₗ ;
    ¬_  to ¬ₗ_ ;
    _∧_ to _∧ₗ_ ;
    _∨_ to _∨ₗ_ ;
    _⇒_ to _⇒ₗ_ )
open import Relator.Equals{ℓ}

-- A model decides whether a proposition is true or false
-- Also known as Interpretation, Structure, Model
record Model{ℓₘ} : Set(ℓ Lvl.⊔ ℓₘ) where
  field
    interpretProp : Prop → Bool{ℓ Lvl.⊔ ℓₘ}

-- TODO: Can this be called a "theory" of propositional logic? So that instances of the type Semantics is the "models" of logic?
-- TODO: Now, all the metalogic depends on booleans, which may not be satisfactory
module _ {T : Set(ℓ)} where
  import      Boolean.Operators
  open        Boolean.Operators.Logic

  satisfaction : Model{ℓ} → Formulaₗ(T) → Bool
  satisfaction(𝔐)(• prop) = Model.interpretProp(𝔐) (prop)
  satisfaction(𝔐)(⊤ₗ) = 𝑇
  satisfaction(𝔐)(⊥ₗ) = 𝐹
  satisfaction(𝔐)(¬ₗ φ) = ¬(satisfaction(𝔐)(φ))
  satisfaction(𝔐)(φ₁ ∧ₗ φ₂) = (satisfaction(𝔐)(φ₁)) ∧ (satisfaction(𝔐)(φ₂))
  satisfaction(𝔐)(φ₁ ∨ₗ φ₂) = (satisfaction(𝔐)(φ₁)) ∨ (satisfaction(𝔐)(φ₂))
  satisfaction(𝔐)(φ₁ ⇒ₗ φ₂) = ¬(satisfaction(𝔐)(φ₁)) ∨ (satisfaction(𝔐)(φ₂))

  -- Syntactic details with the relation symbol
  record SatisfactionRelation (Obj : Set(ℓ) → Set(ℓ)) : Set(Lvl.𝐒(ℓ)) where
    field
      _⊧_ : Model{ℓ} → Obj(Formulaₗ(T)) → Set(ℓ)
  open SatisfactionRelation{{...}} public

  instance
    -- Satisfaction for a single formula
    formula-satisfaction-relation : SatisfactionRelation(id)
    formula-satisfaction-relation = record{_⊧_ = \𝔐 φ → satisfaction(𝔐)(φ) ≡ 𝑇}

  instance
    -- Satisfaction for a list of formulas
    list-satisfaction-relation : SatisfactionRelation(List)
    list-satisfaction-relation = record{_⊧_ = \𝔐 Γ → (∀{γ} → (γ ∈ Γ) → satisfaction(𝔐)(γ) ≡ 𝑇)}

  -- Entailment
  data _⊨_ (Γ : List(Formulaₗ(T))) (φ : Formulaₗ(T)) : Set(ℓ) where
    [⊨]-construct : (∀{𝔐} → (𝔐 ⊧ Γ) → (𝔐 ⊧ φ)) → (Γ ⊨ φ)

  [⊨]-elim : ∀{Γ}{φ} → (Γ ⊨ φ) → Set(ℓ)
  [⊨]-elim {∅}     {φ} ([⊨]-construct proof) = ∀{𝔐 : Model} → (𝔐 ⊧ φ)
  [⊨]-elim {γ ⊰ Γ} {φ} ([⊨]-construct proof) = ∀{𝔐 : Model} → (foldᵣ-init (_⨯_) (𝔐 ⊧ γ) (map (γ ↦ (𝔐 ⊧ γ)) Γ)) → (𝔐 ⊧ φ)

  _⊭_ : List(Formulaₗ(T)) → Formulaₗ(T) → Set(ℓ)
  _⊭_ Γ φ = (_⊨_ Γ φ) → Empty{ℓ}

  -- Validity
  valid : Formulaₗ(T) → Set(ℓ)
  valid = (∅ ⊨_)

  module Theorems where
    [⊤]-entailment : (∅ ⊨ ⊤ₗ)
    [⊤]-entailment = [⊨]-construct(const [≡]-intro)
    -- ∅ ⊨ ⊤ₗ
    -- ∀{𝔐} → (𝔐 ⊧ ∅) → (𝔐 ⊧ ⊤ₗ)
    -- ∀{𝔐} → (𝔐 ⊧ ∅) → (satisfaction(𝔐)(⊤ₗ) ≡ 𝑇)
    -- ∀{𝔐} → (∀{γ} → (γ ∈ ∅) → satisfaction(𝔐)(γ) ≡ 𝑇) → (satisfaction(𝔐)(⊤ₗ) ≡ 𝑇)

    [∧]-entailment : ∀{φ₁ φ₂} → ([ φ₁ ⊰ φ₂ ] ⊨ (φ₁ ∧ₗ φ₂))
    [∧]-entailment{φ₁}{φ₂} = [⊨]-construct ([∈]-proof ↦ [≡]-operation ([∈]-proof ([∈]-use)) ([∈]-proof ([∈]-skip [∈]-use)) {_∧_})
    -- [ φ₁ ⊰ φ₂ ] ⊨ (φ₁ ∧ φ₂)
    -- ∀{𝔐} → (𝔐 ⊧ [ φ₁ ⊰ φ₂ ]) → (𝔐 ⊧ (φ₁ ∧ φ₂))
    -- ∀{𝔐} → (𝔐 ⊧ [ φ₁ ⊰ φ₂ ]) → (satisfaction(𝔐)(φ₁ ∧ₗ φ₂) ≡ 𝑇)
    -- ∀{𝔐} → (𝔐 ⊧ [ φ₁ ⊰ φ₂ ]) → (satisfaction(𝔐)(φ₁) ∧ satisfaction(𝔐)(φ₂) ≡ 𝑇)
    -- ∀{𝔐} → (∀{γ} → (γ ∈ [ φ₁ ⊰ φ₂ ]) → satisfaction(𝔐)(γ) ≡ 𝑇) → (satisfaction(𝔐)(φ₁) ∧ satisfaction(𝔐)(φ₂) ≡ 𝑇)
