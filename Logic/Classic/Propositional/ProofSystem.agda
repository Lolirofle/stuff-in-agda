module Logic.Classic.Propositional.ProofSystem {ℓₚ} (Prop : Set(ℓₚ)) where

import      Level as Lvl
open import Data
open import List
import      List.Theorems
open        List.Theorems.Sets{ℓₚ}{ℓₚ}
open        List.Theorems.Sets.Relators{ℓₚ}{ℓₚ}
open import Logic.Classic.Propositional.Syntax(Prop)
open import Functional

module Meta (_⊢_ : List(Formula) → Formula → Set(ℓₚ)) where
  _⊬_ : List(Formula) → Formula → Set(ℓₚ)
  _⊬_ Γ φ = (_⊢_ Γ φ) → Empty{ℓₚ}

  -- Consistency
  Inconsistent : List(Formula) → Set(ℓₚ)
  Inconsistent Γ = (Γ ⊢ ⊥)

  Consistent : List(Formula) → Set(ℓₚ)
  Consistent Γ = (Γ ⊬ ⊥)

  record [⊢]-rules : Set(ℓₚ) where
    field
      [⊢][⊤]-intro : ∀{Γ} → (Γ ⊢ ⊤)

      [⊢][⊥]-intro : ∀{Γ}{φ} → ((φ ⊰ (¬ φ) ⊰ Γ) ⊢ ⊥)
      [⊢][⊥]-elim  : ∀{Γ}{φ} → ((⊥ ⊰ Γ) ⊢ φ)

      [⊢][¬]-intro : ∀{Γ}{φ} → ((φ ⊰ Γ) ⊢ ⊥) → (Γ ⊢ (¬ φ))
      [⊢][¬]-elim  : ∀{Γ}{φ} → (((¬ φ) ⊰ Γ) ⊢ ⊥) → (Γ ⊢ φ)

      [⊢][∧]-intro : ∀{Γ}{φ₁ φ₂} → ((φ₁ ⊰ φ₂ ⊰ Γ) ⊢ (φ₁ ∧ φ₂))
      [⊢][∧]-elimₗ  : ∀{Γ}{φ₁ φ₂} → (((φ₁ ∧ φ₂) ⊰ Γ) ⊢ φ₁)
      [⊢][∧]-elimᵣ  : ∀{Γ}{φ₁ φ₂} → (((φ₁ ∧ φ₂) ⊰ Γ) ⊢ φ₂)

      [⊢][∨]-introₗ : ∀{Γ}{φ₁ φ₂} → ((φ₁ ⊰ Γ) ⊢ (φ₁ ∨ φ₂))
      [⊢][∨]-introᵣ : ∀{Γ}{φ₁ φ₂} → ((φ₂ ⊰ Γ) ⊢ (φ₁ ∨ φ₂))
      [⊢][∨]-elim   : ∀{Γ₁ Γ₂}{φ₁ φ₂ φ₃} → ((φ₁ ⊰ Γ₁) ⊢ φ₃) → ((φ₂ ⊰ Γ₂) ⊢ φ₃) → (((φ₁ ∨ φ₂) ⊰ (Γ₁ ++ Γ₂)) ⊢ φ₃)

      [⊢][⇒]-intro : ∀{Γ}{φ₁ φ₂} → ((φ₁ ⊰ Γ) ⊢ φ₂) → (Γ ⊢ (φ₁ ⇒ φ₂))
      [⊢][⇒]-elim  : ∀{Γ}{φ₁ φ₂} → (((φ₁ ⇒ φ₂) ⊰ (φ₁) ⊰ Γ) ⊢ φ₂)

  record [⊢]-deduction : Set(ℓₚ) where
    field
      [⊢][⊤]-intro : ∀{Γ} → (Γ ⊢ ⊤)

      [⊢][⊥]-intro : ∀{Γ}{φ} → (φ ∈ Γ) → ((¬ φ) ∈ Γ) → (Γ ⊢ ⊥)
      [⊢][⊥]-elim  : ∀{Γ}{φ} → (⊥ ∈ Γ) → (Γ ⊢ φ)

      [⊢][¬]-intro : ∀{Γ}{φ} → ((φ ∈ Γ) → (Γ ⊢ ⊥)) → (Γ ⊢ (¬ φ))
      [⊢][¬]-elim  : ∀{Γ}{φ} → (((¬ φ) ∈ Γ) → (Γ ⊢ ⊥)) → (Γ ⊢ φ)

      [⊢][∧]-intro : ∀{Γ}{φ₁ φ₂} → (φ₁ ∈ Γ) → (φ₂ ∈ Γ) → (Γ ⊢ (φ₁ ∧ φ₂))
      [⊢][∧]-elimₗ  : ∀{Γ}{φ₁ φ₂} → ((φ₁ ∧ φ₂) ∈ Γ) → (Γ ⊢ φ₁)
      [⊢][∧]-elimᵣ  : ∀{Γ}{φ₁ φ₂} → ((φ₁ ∧ φ₂) ∈ Γ) → (Γ ⊢ φ₂)

      [⊢][∨]-introₗ : ∀{Γ}{φ₁ φ₂} → (φ₁ ∈ Γ) → (Γ ⊢ (φ₁ ∨ φ₂))
      [⊢][∨]-introᵣ : ∀{Γ}{φ₁ φ₂} → (φ₂ ∈ Γ) → (Γ ⊢ (φ₁ ∨ φ₂))
      [⊢][∨]-elim   : ∀{Γ₁ Γ₂}{φ₁ φ₂ φ₃} → ((φ₁ ∈ Γ₁) → (Γ₁ ⊢ φ₃)) → ((φ₂ ∈ Γ₂) → (Γ₂ ⊢ φ₃)) → ((φ₁ ∨ φ₂) ∈ (Γ₁ ++ Γ₂)) → ((Γ₁ ++ Γ₂) ⊢ φ₃)

      [⊢][⇒]-intro : ∀{Γ}{φ₁ φ₂} → ((φ₁ ∈ Γ) → (Γ ⊢ φ₂)) → (Γ ⊢ (φ₁ ⇒ φ₂))
      [⊢][⇒]-elim  : ∀{Γ}{φ₁ φ₂} → ((φ₁ ⇒ φ₂) ∈ Γ) → (φ₁ ∈ Γ) → (Γ ⊢ φ₂)

module TruthTables where
  open Meta

module NaturalDeduction where
  {-# NO_POSITIVITY_CHECK #-} -- TODO: Could this make deriving ⊥ possible?
  data Tree : Formula → Set(ℓₚ) where
    [⊤]-intro : Tree(⊤)

    [⊥]-intro : ∀{φ} → Tree(φ) → Tree(¬ φ) → Tree(⊥)

    [¬]-intro : ∀{φ} → (Tree(φ) → Tree(⊥)) → Tree(¬ φ)
    [¬]-elim  : ∀{φ} → (Tree(¬ φ) → Tree(⊥)) → Tree(φ)

    [∧]-intro : ∀{φ₁ φ₂} → Tree(φ₁) → Tree(φ₂) → Tree(φ₁ ∧ φ₂)
    [∧]-elimₗ  : ∀{φ₁ φ₂} → Tree(φ₁ ∧ φ₂) → Tree(φ₁)
    [∧]-elimᵣ  : ∀{φ₁ φ₂} → Tree(φ₁ ∧ φ₂) → Tree(φ₂)

    [∨]-introₗ : ∀{φ₁ φ₂} → Tree(φ₁) → Tree(φ₁ ∨ φ₂)
    [∨]-introᵣ : ∀{φ₁ φ₂} → Tree(φ₂) → Tree(φ₁ ∨ φ₂)
    [∨]-elim  : ∀{φ₁ φ₂ φ₃} → (Tree(φ₁) → Tree(φ₃)) → (Tree(φ₂) → Tree(φ₃)) → Tree(φ₃)

    [⇒]-intro : ∀{φ₁ φ₂} → (Tree(φ₁) → Tree(φ₂)) → Tree(φ₁ ⇒ φ₂)
    [⇒]-elim  : ∀{φ₁ φ₂} → Tree(φ₁ ⇒ φ₂) → Tree(φ₁) → Tree(φ₂)

  -- Double negated proposition is positive
  [¬¬]-elim : ∀{φ} → Tree(¬ (¬ φ)) → Tree(φ)
  [¬¬]-elim nna = [¬]-elim(na ↦ [⊥]-intro na nna)

  [⊥]-elim : ∀{φ} → Tree(⊥) → Tree(φ)
  [⊥]-elim bottom = [¬]-elim(_ ↦ bottom)

  Trees : List(Formula) → Set(ℓₚ)
  Trees(Γ) = (∀{γ} → (γ ∈ Γ) → Tree(γ))

  -- Derivability
  -- Proof of: If there exists a tree for every formula in Γ, then there exists a tree for the formula φ.
  data _⊢_ (Γ : List(Formula)) (φ : Formula) : Set(ℓₚ) where
    [⊢]-construct : (Trees(Γ) → Tree(φ)) → (Γ ⊢ φ)

  module Theorems where
    open [∈]-proof {Formula}
    open Meta(_⊢_)

    -- Trees-proof-by-[∈]-fn : ∀{Γ₁ Γ₂} → (∀{a} → (a ∈ Γ₁) → (a ∈ Γ₂)) → (Trees(Γ₂) → Trees(Γ₁))
    -- Trees-proof-by-[∈]-fn = liftᵣ

    Trees-fewer : ∀{Γ}{φ} → Trees(φ ⊰ Γ) → Trees(Γ)
    Trees-fewer(φ⊰Γ) = [∈]-with-[⊰][→] (φ⊰Γ)

    Trees-formula-weakening : ∀{ℓ}{T : Set(ℓ)}{Γ} → (Trees(Γ) → T) → ∀{φ} → (Trees(φ ⊰ Γ) → T)
    Trees-formula-weakening(φ→T) (φ⊰Γ) = (φ→T) (Trees-fewer (φ⊰Γ))

    Trees-[++]-commutativity : ∀{Γ₁ Γ₂} → Trees(Γ₁ ++ Γ₂) → Trees(Γ₂ ++ Γ₁)
    Trees-[++]-commutativity {Γ₁}{Γ₂} (trees) = trees ∘ ([∈][++]-commutativity{_}{Γ₂}{Γ₁})

    -- Trees-reorderₗ : ∀{Γ₁ Γ₂}{φ} → Trees(Γ₁ ++ (φ ⊰ Γ₂)) → Trees(φ ⊰ (Γ₁ ++ Γ₂))
    -- Trees-reorderₗ (Γ₁φΓ₂) = [≡]-substitution (Trees-[++]-commutativity (Trees-[++]-commutativity (Γ₁φΓ₂)))
    -- Γ₁ ++ (φ ⊰ Γ₂) //assumption
    -- (φ ⊰ Γ₂) ++ Γ₁ //Trees-[++]-commutativity
    -- φ ⊰ (Γ₂ ++ Γ₁) //Definition: (++)
    -- φ ⊰ (Γ₁ ++ Γ₂) //[≡]-substitution (Trees-[++]-commutativity)

    -- Trees-[++]-duplicate : ∀{Γ} → Trees(Γ ++ Γ) → Trees(Γ)
    -- Trees-[++]-duplicate {Γ} (trees) = \{γ} → liftᵣ([∈][++]-duplicate)(trees{γ})

    [⊢]-tree-rule : ∀{Γ₁ Γ₂}{φ} → (Trees(Γ₂) → Trees(Γ₁)) → (Γ₁ ⊢ φ) → (Γ₂ ⊢ φ)
    [⊢]-tree-rule (trees-fn) ([⊢]-construct (Γ₁⊢φ)) = [⊢]-construct ((Γ₁⊢φ) ∘ (trees-fn))

    [⊢]-formula-weakening : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ φ₁) → ((φ₂ ⊰ Γ) ⊢ φ₁)
    [⊢]-formula-weakening {_}{_}{φ₂} = [⊢]-tree-rule (Trees-fewer {_}{φ₂})
    -- [⊢]-formula-weakening : ∀{Γ}{φ₁} → (Γ ⊢ φ₁) → ∀{φ₂} → ((φ₂ ⊰ Γ) ⊢ φ₁)
    -- [⊢]-formula-weakening ([⊢]-construct (Γ⊢φ₁)) = [⊢]-construct (Trees-formula-weakening(Γ⊢φ₁))
    -- ∀{Γ}{φ₁} → (Trees(Γ) → Tree(φ₁))   →   ∀{φ₂} → (Trees(φ₂ ⊰ Γ) → Tree(φ₁))
    -- ∀{Γ}{φ₁} → ((∀{γ} → (γ ∈ Γ) → Tree(γ)) → Tree(φ₁))   →   ∀{φ₂} → ((∀{γ} → (γ ∈ (φ₂ ⊰ Γ)) → Tree(γ)) → Tree(φ₁))

    [⊢]-weakeningₗ : ∀{Γ₂}{φ} → (Γ₂ ⊢ φ) → ∀{Γ₁} → ((Γ₁ ++ Γ₂) ⊢ φ)
    [⊢]-weakeningₗ {_} {_} (Γ₂⊢φ) {∅}       = (Γ₂⊢φ)
    [⊢]-weakeningₗ {Γ₂}{φ} (Γ₂⊢φ) {φ₂ ⊰ Γ₁} = [⊢]-formula-weakening {Γ₁ ++ Γ₂} ([⊢]-weakeningₗ (Γ₂⊢φ) {Γ₁})

    [⊢]-reorder-[++] : ∀{Γ₁ Γ₂}{φ} → ((Γ₁ ++ Γ₂) ⊢ φ) → ((Γ₂ ++ Γ₁) ⊢ φ)
    [⊢]-reorder-[++] {Γ₁}{Γ₂} = [⊢]-tree-rule (Trees-[++]-commutativity {Γ₂}{Γ₁})

    -- [⊢]-reorder-first : ∀{Γ₁ Γ₂}{φ₁ φ₂} → ((Γ₁ ++ (φ₁ ⊰ Γ₂)) ⊢ φ₂) → ((φ₁ ⊰ (Γ₁ ++ Γ₂)) ⊢ φ₂)
    -- [⊢]-reorder-first {Γ₁}{Γ₂} = 

    [⊢]-id : ∀{φ} → ([ φ ] ⊢ φ)
    [⊢]-id = [⊢]-construct ([∈]-proof ↦ [∈]-proof ([∈]-use))
    -- ((A → B) → B) → C
    -- f(g ↦ g(x))

    [⊢][⊤]-intro : (∅ ⊢ ⊤)
    [⊢][⊤]-intro = [⊢]-construct (const [⊤]-intro)

module NaturalDeductionDerivability where
  open Meta

  data _⊢_ : List(Formula) → Formula → Set(ℓₚ) where
    id-intro : ∀{φ} → ([ φ ] ⊢ φ)

    [⊤]-intro : (∅ ⊢ ⊤)

    [⊥]-intro : ∀{Γ₁ Γ₂}{φ} → ((Γ₁ ⊢ φ) ⨯ (Γ₂ ⊢ (¬ φ))) → ((Γ₁ ++ Γ₂) ⊢ ⊥)

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
