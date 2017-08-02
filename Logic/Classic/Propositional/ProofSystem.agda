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

-- Natural deduction proof trees.
-- This is a proof system that should reflect the semantic truth of formulas.
module NaturalDeduction where
  -- A `Tree` is associated with a formula.
  -- [Proposition without assumptions (Axiom)]
  --   Represented by the type `Tree(φ)`.
  --   It means that a tree with the formula φ at the bottom exists (is constructable).
  --   This represents that the formula φ is provable in the natural deduction proof system.
  -- [Proposition with an assumption]
  --   Represented by the type `Tree(φ₁) → Tree(φ₂)`.
  --   It means that a tree with φ₁ as a leaf and φ₂ at the bottom exists (is constructable).
  --   This represents that the formula φ₂ is provable if one can assume the formula φ₁.
  -- The constructors of `Tree` are all the possible ways to construct a natural deduction proof tree.
  -- If a tree with a certain formula cannot be constructed, then it means that the formula is not provable.
  {-# NO_POSITIVITY_CHECK #-} -- TODO: Could this be a problem?
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
    [∨]-elim  : ∀{φ₁ φ₂ φ₃} → Tree(φ₁ ∨ φ₂) → (Tree(φ₁) → Tree(φ₃)) → (Tree(φ₂) → Tree(φ₃)) → Tree(φ₃)

    [⇒]-intro : ∀{φ₁ φ₂} → (Tree(φ₁) → Tree(φ₂)) → Tree(φ₁ ⇒ φ₂)
    [⇒]-elim  : ∀{φ₁ φ₂} → Tree(φ₁ ⇒ φ₂) → Tree(φ₁) → Tree(φ₂)

  -- Double negated proposition is positive.
  [¬¬]-elim : ∀{φ} → Tree(¬ (¬ φ)) → Tree(φ)
  [¬¬]-elim nna = [¬]-elim(na ↦ [⊥]-intro na nna)

  -- A contradiction can derive every formula.
  [⊥]-elim : ∀{φ} → Tree(⊥) → Tree(φ)
  [⊥]-elim bottom = [¬]-elim(_ ↦ bottom)

  -- List of natural deduction proof trees.
  -- A `Trees` is associated with a list of formulas.
  -- If all formulas in the list can be constructed, then all the formulas in the list are provable.
  -- This is used to express (⊢) using the usual conventions in formal logic.
  Trees : List(Formula) → Set(ℓₚ)
  Trees(Γ) = (∀{γ} → (γ ∈ Γ) → Tree(γ))

  -- Derivability
  -- Proof of: If there exists a tree for every formula in Γ, then there exists a tree for the formula φ.
  data _⊢_ (Γ : List(Formula)) (φ : Formula) : Set(ℓₚ) where
    [⊢]-construct : (Trees(Γ) → Tree(φ)) → (Γ ⊢ φ)

  module Theorems where
    open [∈]-proof {Formula}
    open Meta(_⊢_)

    Tree-to-Trees : ∀{φ} → Tree(φ) → Trees([ φ ])
    Tree-to-Trees (φ-tree) ([∈]-use) = φ-tree
    Tree-to-Trees (φ-tree) ([∈]-skip ())

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

    Trees-[++]-duplicate : ∀{Γ} → Trees(Γ ++ Γ) → Trees(Γ)
    Trees-[++]-duplicate {Γ} (trees) = \{γ} → liftᵣ([∈][++]-expandₗ {γ}{Γ}{Γ})(trees{γ})

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
    [⊢][⊤]-intro = [⊢]-construct
      (const [⊤]-intro)

    [⊢][⊥]-intro : ∀{φ} → ([ φ ⊰ (¬ φ) ] ⊢ ⊥)
    [⊢][⊥]-intro = [⊢]-construct
      ([∈]-to-tree ↦ [⊥]-intro
        ([∈]-to-tree ([∈]-use))
        ([∈]-to-tree ([∈]-skip [∈]-use))
      )

    [⊢][¬]-intro : ∀{φ} → ([ φ ] ⊢ ⊥) → (∅ ⊢ (¬ φ))
    [⊢][¬]-intro ([⊢]-construct φ⊢⊥) = [⊢]-construct
      ([∈]-to-tree ↦ [¬]-intro
        ((φ⊢⊥)∘(Tree-to-Trees))
      )

    [⊢][¬]-elim : ∀{φ} → ([(¬ φ)] ⊢ ⊥) → (∅ ⊢ φ)
    [⊢][¬]-elim ([⊢]-construct ¬φ⊢⊥) = [⊢]-construct
      ([∈]-to-tree ↦ [¬]-elim
        ((¬φ⊢⊥)∘(Tree-to-Trees))
      )

    [⊢][∧]-intro : ∀{φ₁ φ₂} → ([ φ₁ ⊰ φ₂ ] ⊢ (φ₁ ∧ φ₂))
    [⊢][∧]-intro = [⊢]-construct
      ([∈]-to-tree ↦ [∧]-intro
        ([∈]-to-tree ([∈]-use))
        ([∈]-to-tree ([∈]-skip [∈]-use))
      )

    [⊢][∧]-elimₗ : ∀{φ₁ φ₂} → ([(φ₁ ∧ φ₂)] ⊢ φ₁)
    [⊢][∧]-elimₗ = [⊢]-construct
      ([∈]-to-tree ↦ [∧]-elimₗ
          ([∈]-to-tree ([∈]-use))
      )

    [⊢][∧]-elimᵣ : ∀{φ₁ φ₂} → ([(φ₁ ∧ φ₂)] ⊢ φ₂)
    [⊢][∧]-elimᵣ = [⊢]-construct
      ([∈]-to-tree ↦ [∧]-elimᵣ
        ([∈]-to-tree ([∈]-use))
      )

    [⊢][∨]-introₗ : ∀{φ₁ φ₂} → ([ φ₁ ] ⊢ (φ₁ ∨ φ₂))
    [⊢][∨]-introₗ = [⊢]-construct
      ([∈]-to-tree ↦ [∨]-introₗ
        ([∈]-to-tree ([∈]-use))
      )

    [⊢][∨]-introᵣ : ∀{φ₁ φ₂} → ([ φ₂ ] ⊢ (φ₁ ∨ φ₂))
    [⊢][∨]-introᵣ = [⊢]-construct
      ([∈]-to-tree ↦ [∨]-introᵣ
        ([∈]-to-tree ([∈]-use))
      )

    [⊢][∨]-elim : ∀{φ₁ φ₂ φ₃} → ([ φ₁ ] ⊢ φ₃) → ([ φ₂ ] ⊢ φ₃) → ([(φ₁ ∨ φ₂)] ⊢ φ₃)
    [⊢][∨]-elim ([⊢]-construct φ₁⊢φ₃) ([⊢]-construct φ₂⊢φ₃) = [⊢]-construct
      ([∈]-to-tree ↦ [∨]-elim
        ([∈]-to-tree ([∈]-use))
        ((φ₁⊢φ₃)∘(Tree-to-Trees))
        ((φ₂⊢φ₃)∘(Tree-to-Trees))
      )

    [⊢][⇒]-intro : ∀{φ₁ φ₂} → ([ φ₁ ] ⊢ φ₂) → (∅ ⊢ (φ₁ ⇒ φ₂))
    [⊢][⇒]-intro ([⊢]-construct φ₁⊢φ₂) = [⊢]-construct
      ([∈]-to-tree ↦ [⇒]-intro
        ((φ₁⊢φ₂)∘(Tree-to-Trees))
      )

    [⊢][⇒]-elim : ∀{φ₁ φ₂} → ([ (φ₁ ⇒ φ₂) ⊰ φ₁ ] ⊢ φ₂)
    [⊢][⇒]-elim = [⊢]-construct
      ([∈]-to-tree ↦ [⇒]-elim
        ([∈]-to-tree ([∈]-use))
        ([∈]-to-tree ([∈]-skip [∈]-use))
      )

module NaturalDeductionDerivability where
  open Meta

  data _⊢_ : List(Formula) → Formula → Set(ℓₚ) where
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
