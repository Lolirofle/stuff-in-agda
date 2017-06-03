module Logic.Classic.Propositional.ProofSystem {ℓₚ} (Prop : Set(ℓₚ)) where

import      Level as Lvl
open import Data
open import List
import      List.Theorems
open        List.Theorems.Sets{ℓₚ}{ℓₚ}
open        List.Theorems.Sets.Relators{ℓₚ}{ℓₚ}
open import Logic.Classic.Propositional.Syntax(Prop)
open import Functional

module TruthTables where

module NaturalDeduction where
  {-# NO_POSITIVITY_CHECK #-} -- TODO: Could this make deriving ⊥ possible?
  -- ([⇒]-intro(const Initial)) is possible, which looks a little bit incorrect. This also affects the "initials" function
  data Tree : Formula → Set(ℓₚ) where
    Initial   : ∀{φ} → Tree(φ)

    [⊤]-intro : Tree(⊤)

    [⊥]-intro : ∀{φ} → Tree(φ) → Tree(¬ φ) → Tree(⊥)

    [¬]-intro : ∀{φ} → (Tree(φ) → Tree(⊥)) → Tree(¬ φ)
    [¬]-elim  : ∀{φ} → (Tree(¬ φ) → Tree(⊥)) → Tree(φ)

    [∧]-intro : ∀{φ₁ φ₂} → Tree(φ₁) → Tree(φ₂) → Tree(φ₁ ∧ φ₂)
    [∧]-elimₗ  : ∀{φ₁ φ₂} → Tree(φ₁ ∧ φ₂) → Tree(φ₁)
    [∧]-elimᵣ  : ∀{φ₁ φ₂} → Tree(φ₁ ∧ φ₂) → Tree(φ₂)

    [∨]-introₗ : ∀{φ₁ φ₂} → Tree(φ₁) → Tree(φ₁ ∨ φ₂)
    [∨]-introᵣ : ∀{φ₁ φ₂} → Tree(φ₁) → Tree(φ₁ ∨ φ₂)
    [∨]-elim  : ∀{φ₁ φ₂ φ₃} → (Tree(φ₁) → Tree(φ₃)) → (Tree(φ₂) → Tree(φ₃)) → Tree(φ₃)

    [⇒]-intro : ∀{φ₁ φ₂} → (Tree(φ₁) → Tree(φ₂)) → Tree(φ₁ ⇒ φ₂)
    [⇒]-elim  : ∀{φ₁ φ₂} → Tree(φ₁ ⇒ φ₂) → Tree(φ₁) → Tree(φ₂)

  -- Double negated proposition is positive
  [¬¬]-elim : ∀{φ} → Tree(¬ (¬ φ)) → Tree(φ)
  [¬¬]-elim nna = [¬]-elim(na ↦ [⊥]-intro na nna)

  [⊥]-elim : ∀{φ} → Tree(⊥) → Tree(φ)
  [⊥]-elim bottom = [¬]-elim(_ ↦ bottom)

  initials : ∀{φ} → Tree(φ) → List(Formula)
  initials(Initial{φ})             = singleton(φ)
  initials([⊤]-intro)              = ∅
  initials([⊥]-intro a b)          = initials(a) ++ initials(b)
  initials([¬]-intro{φ}(_))        = singleton(φ)
  initials([¬]-elim{φ}(_))         = singleton(¬ φ)
  initials([∧]-intro a b)          = initials(a) ++ initials(b)
  initials([∧]-elimₗ a)            = initials(a)
  initials([∧]-elimᵣ a)            = initials(a)
  initials([∨]-introₗ a)           = initials(a)
  initials([∨]-introᵣ a)           = initials(a)
  initials([∨]-elim{φ₁}{φ₂}(_)(_)) = [ φ₁ ⊰ φ₂ ]
  initials([⇒]-intro{φ}(_))        = singleton(φ)
  initials([⇒]-elim a b)           = initials(a) ++ initials(b)

  -- Derivability
  data _⊢_ (Γ : List(Formula)) (φ : Formula) : Set(ℓₚ) where
    [⊢]-construct : (∀{木 : Tree(φ)} → (initials(木) ⊆ Γ)) → (Γ ⊢ φ)

  _⊬_ : List(Formula) → Formula → Set(ℓₚ)
  _⊬_ Γ φ = (_⊢_ Γ φ) → Empty{ℓₚ}

  -- Consistency
  inconsistent : List(Formula) → Set(ℓₚ)
  inconsistent Γ = (Γ ⊢ ⊥)

  consistent : List(Formula) → Set(ℓₚ)
  consistent Γ = (Γ ⊬ ⊥)

module NaturalDeductionDerivability where
  data _⊢_ : List(Formula) → Formula → Set(ℓₚ) where
    formula-intro : ∀{φ} → ([ φ ] ⊢ φ)

    [⊤]-intro : (∅ ⊢ ⊤)

    [⊥]-intro : ∀{Γ}{φ} → ((Γ ⊢ φ) ⨯ (Γ ⊢ (¬ φ))) → (Γ ⊢ ⊥)

    [¬]-intro : ∀{Γ}{φ} → ((φ ⊰ Γ) ⊢ ⊥) → (Γ ⊢ (¬ φ))
    [¬]-elim  : ∀{Γ}{φ} → (((¬ φ) ⊰ Γ) ⊢ ⊥) → (Γ ⊢ φ)

    [∧]-intro : ∀{Γ₁ Γ₂}{φ₁ φ₂} → ((Γ₁ ⊢ φ₁) ⨯ (Γ₂ ⊢ φ₂)) → ((Γ₁ ++ Γ₂) ⊢ (φ₁ ∧ φ₂))
    [∧]-elimₗ  : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ (φ₁ ∧ φ₂)) → (Γ ⊢ φ₁)
    [∧]-elimᵣ  : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ (φ₁ ∧ φ₂)) → (Γ ⊢ φ₂)

    [∨]-introₗ : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ φ₁) → (Γ ⊢ (φ₁ ∨ φ₂))
    [∨]-introᵣ : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ φ₂) → (Γ ⊢ (φ₁ ∨ φ₂))
    [∨]-elim  : ∀{Γ₁ Γ₂ Γ₃}{φ₁ φ₂ φ₃} → (((φ₁ ⊰ Γ₁) ⊢ φ₃) ⨯ ((φ₂ ⊰ Γ₂) ⊢ φ₃) ⨯ (Γ₃ ⊢ (φ₁ ∨ φ₂))) → ((Γ₁ ++ Γ₂ ++ Γ₃) ⊢ φ₃)

    [⇒]-intro : ∀{Γ}{φ₁ φ₂} → ((φ₁ ⊰ Γ) ⊢ φ₂) → (Γ ⊢ (φ₁ ⇒ φ₂))
    [⇒]-elim  : ∀{Γ₁ Γ₂}{φ₁ φ₂} → ((Γ₁ ⊢ (φ₁ ⇒ φ₂)) ⨯ (Γ₂ ⊢ φ₁)) → ((Γ₁ ++ Γ₂) ⊢ φ₂)
