module Logic.Classic.Propositional.ProofSystem {ℓₚ} (Prop : Set(ℓₚ)) where

import      Level as Lvl
open import Data
import      List
open        List using (List ; ∅ ; _⊰_ ; _++_ ; [_ ; _])
import      Sets.ListSet
open        Sets.ListSet{ℓₚ}{ℓₚ}
open        Sets.ListSet.Relators{ℓₚ}{ℓₚ}
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
      [⊤]-intro : ∀{Γ} → (Γ ⊢ ⊤)

      [⊥]-intro : ∀{Γ}{φ} → ((φ ⊰ (¬ φ) ⊰ Γ) ⊢ ⊥)
      [⊥]-elim  : ∀{Γ}{φ} → ((⊥ ⊰ Γ) ⊢ φ)

      [¬]-intro : ∀{Γ}{φ} → ((φ ⊰ Γ) ⊢ ⊥) → (Γ ⊢ (¬ φ))
      [¬]-elim  : ∀{Γ}{φ} → (((¬ φ) ⊰ Γ) ⊢ ⊥) → (Γ ⊢ φ)

      [∧]-intro : ∀{Γ}{φ₁ φ₂} → ((φ₁ ⊰ φ₂ ⊰ Γ) ⊢ (φ₁ ∧ φ₂))
      [∧]-elimₗ  : ∀{Γ}{φ₁ φ₂} → (((φ₁ ∧ φ₂) ⊰ Γ) ⊢ φ₁)
      [∧]-elimᵣ  : ∀{Γ}{φ₁ φ₂} → (((φ₁ ∧ φ₂) ⊰ Γ) ⊢ φ₂)

      [∨]-introₗ : ∀{Γ}{φ₁ φ₂} → ((φ₁ ⊰ Γ) ⊢ (φ₁ ∨ φ₂))
      [∨]-introᵣ : ∀{Γ}{φ₁ φ₂} → ((φ₂ ⊰ Γ) ⊢ (φ₁ ∨ φ₂))
      [∨]-elim   : ∀{Γ₁ Γ₂}{φ₁ φ₂ φ₃} → ((φ₁ ⊰ Γ₁) ⊢ φ₃) → ((φ₂ ⊰ Γ₂) ⊢ φ₃) → (((φ₁ ∨ φ₂) ⊰ (Γ₁ ++ Γ₂)) ⊢ φ₃)

      [⇒]-intro : ∀{Γ}{φ₁ φ₂} → ((φ₁ ⊰ Γ) ⊢ φ₂) → (Γ ⊢ (φ₁ ⇒ φ₂))
      [⇒]-elim  : ∀{Γ}{φ₁ φ₂} → (((φ₁ ⇒ φ₂) ⊰ (φ₁) ⊰ Γ) ⊢ φ₂)

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

  module Trees where
    open [∈]-proof {Formula}

    empty : Trees(∅)
    empty ()

    singleton : ∀{φ} → Tree(φ) → Trees([ φ ])
    singleton (φ-tree) ([∈]-use) = φ-tree
    singleton (φ-tree) ([∈]-skip ())

    -- TODO: This could possibly be generalized to: ∀{Γ₁ Γ₂}{F : T → Set} → (∀{a} → (a ∈ Γ₁) → (a ∈ Γ₂)) → ((∀{γ} → (γ ∈ Γ₂) → F(γ)) → (∀{γ} → (γ ∈ Γ₁) → F(γ)))
    from-[∈] : ∀{Γ₁ Γ₂} → (∀{a} → (a ∈ Γ₁) → (a ∈ Γ₂)) → (Trees(Γ₂) → Trees(Γ₁))
    from-[∈] (f) (Γ₂-trees) {γ} = liftᵣ (f{γ}) (Γ₂-trees)

    push : ∀{Γ}{φ} → Tree(φ) → Trees(Γ) → Trees(φ ⊰ Γ)
    push (φ-tree) (Γ-tree) ([∈]-use) = φ-tree
    push (φ-tree) (Γ-tree) ([∈]-skip inclusion) = Γ-tree (inclusion)

    pop : ∀{Γ}{φ} → Trees(φ ⊰ Γ) → Trees(Γ)
    pop = from-[∈] ([∈]-skip)

    -- TODO: Could be removed because liftᵣ is easier to use. ALthough a note/tip should be written for these purposes.
    -- formula-weaken : ∀{ℓ}{T : Set(ℓ)}{Γ₁ Γ₂} → (Trees(Γ₁) → Trees(Γ₂)) → (Trees(Γ₂) → T) → (Trees(Γ₁) → T)
    -- formula-weaken = liftᵣ

    [++]-commute : ∀{Γ₁ Γ₂} → Trees(Γ₁ ++ Γ₂) → Trees(Γ₂ ++ Γ₁)
    [++]-commute {Γ₁}{Γ₂} (trees) = trees ∘ ([∈][++]-commute{_}{Γ₂}{Γ₁})

    [++]-left : ∀{Γ₁ Γ₂} → Trees(Γ₁ ++ Γ₂) → Trees(Γ₁)
    [++]-left {Γ₁}{Γ₂} (trees) ([∈]-[Γ₁]) = trees ([∈][++]-expandᵣ {_}{Γ₁}{Γ₂} [∈]-[Γ₁])

    [++]-right : ∀{Γ₁ Γ₂} → Trees(Γ₁ ++ Γ₂) → Trees(Γ₂)
    [++]-right {Γ₁}{Γ₂} (trees) ([∈]-[Γ₂]) = trees ([∈][++]-expandₗ {_}{Γ₁}{Γ₂} [∈]-[Γ₂])

    [++]-deduplicate : ∀{Γ} → Trees(Γ ++ Γ) → Trees(Γ)
    [++]-deduplicate {Γ} (trees) = \{γ} → liftᵣ([∈][++]-expandₗ {γ}{Γ}{Γ})(trees{γ})

    -- [⊰]-reorderₗ : ∀{Γ₁ Γ₂}{φ} → Trees(Γ₁ ++ (φ ⊰ Γ₂)) → Trees(φ ⊰ (Γ₁ ++ Γ₂))
    -- [⊰]-reorderₗ (Γ₁φΓ₂-trees) = 
    -- Γ₁ ++ (φ ⊰ Γ₂) //assumption
    -- (φ ⊰ Γ₂) ++ Γ₁ //Trees.[++]-commute
    -- φ ⊰ (Γ₂ ++ Γ₁) //Definition: (++)
    -- φ ⊰ (Γ₁ ++ Γ₂) //[≡]-substitution (Trees.[++]-commute)

  -- Derivability
  -- Proof of: If there exists a tree for every formula in Γ, then there exists a tree for the formula φ.
  data _⊢_ (Γ : List(Formula)) (φ : Formula) : Set(ℓₚ) where
    [⊢]-construct : (Trees(Γ) → Tree(φ)) → (Γ ⊢ φ)

  module Theorems where
    open [∈]-proof {Formula}

    [⊢]-from-trees : ∀{Γ₁ Γ₂}{φ} → (Trees(Γ₂) → Trees(Γ₁)) → (Γ₁ ⊢ φ) → (Γ₂ ⊢ φ)
    [⊢]-from-trees (trees-fn) ([⊢]-construct (Γ₁⊢φ)) = [⊢]-construct ((Γ₁⊢φ) ∘ (trees-fn))

    [⊢]-formula-weaken : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ φ₁) → ((φ₂ ⊰ Γ) ⊢ φ₁)
    [⊢]-formula-weaken {_}{_}{φ₂} = [⊢]-from-trees (Trees.pop {_}{φ₂})

    [⊢]-weakenₗ : ∀{Γ₂}{φ} → (Γ₂ ⊢ φ) → ∀{Γ₁} → ((Γ₁ ++ Γ₂) ⊢ φ)
    [⊢]-weakenₗ {_} {_} (Γ₂⊢φ) {∅}       = (Γ₂⊢φ)
    [⊢]-weakenₗ {Γ₂}{φ} (Γ₂⊢φ) {φ₂ ⊰ Γ₁} = [⊢]-formula-weaken {Γ₁ ++ Γ₂} ([⊢]-weakenₗ (Γ₂⊢φ) {Γ₁})

    [⊢]-reorder-[++] : ∀{Γ₁ Γ₂}{φ} → ((Γ₁ ++ Γ₂) ⊢ φ) → ((Γ₂ ++ Γ₁) ⊢ φ)
    [⊢]-reorder-[++] {Γ₁}{Γ₂} = [⊢]-from-trees (Trees.[++]-commute {Γ₂}{Γ₁})

    -- [⊢]-reorder-first : ∀{Γ₁ Γ₂}{φ₁ φ₂} → ((Γ₁ ++ (φ₁ ⊰ Γ₂)) ⊢ φ₂) → ((φ₁ ⊰ (Γ₁ ++ Γ₂)) ⊢ φ₂)
    -- [⊢]-reorder-first {Γ₁}{Γ₂} = [⊢]-reorder-[++]

    [⊢]-id : ∀{Γ}{φ} → ((φ ⊰ Γ) ⊢ φ)
    [⊢]-id = [⊢]-construct ([∈]-proof ↦ [∈]-proof ([∈]-use))
    -- ((A → B) → B) → C
    -- f(g ↦ g(x))

    [⊢][⊤]-intro : ∀{Γ} → (Γ ⊢ ⊤)
    [⊢][⊤]-intro = [⊢]-construct
      (const [⊤]-intro)

    [⊢][⊥]-intro : ∀{Γ}{φ} → ((φ ⊰ (¬ φ) ⊰ Γ) ⊢ ⊥)
    [⊢][⊥]-intro = [⊢]-construct
      (assumption-trees ↦ [⊥]-intro
        (assumption-trees ([∈]-use))
        (assumption-trees ([∈]-skip [∈]-use))
      )

    [⊢][⊥]-elim : ∀{Γ}{φ} → ((⊥ ⊰ Γ) ⊢ φ)
    [⊢][⊥]-elim = [⊢]-construct
      (assumption-trees ↦ [⊥]-elim
        (assumption-trees ([∈]-use))
      )

    [⊢][¬]-intro : ∀{Γ}{φ} → ((φ ⊰ Γ) ⊢ ⊥) → (Γ ⊢ (¬ φ))
    [⊢][¬]-intro ([⊢]-construct φΓ⊢⊥) = [⊢]-construct
      (assumption-trees ↦ [¬]-intro
        (φ-tree ↦ (φΓ⊢⊥) (Trees.push (φ-tree) (\{γ} → assumption-trees {γ})))
      )

    [⊢][¬]-elim : ∀{Γ}{φ} → (((¬ φ) ⊰ Γ) ⊢ ⊥) → (Γ ⊢ φ)
    [⊢][¬]-elim ([⊢]-construct ¬φΓ⊢⊥) = [⊢]-construct
      (assumption-trees ↦ [¬]-elim
        (φ-tree ↦ (¬φΓ⊢⊥) (Trees.push (φ-tree) (\{γ} → assumption-trees {γ})))
      )

    [⊢][∧]-intro : ∀{Γ}{φ₁ φ₂} → ((φ₁ ⊰ φ₂ ⊰ Γ) ⊢ (φ₁ ∧ φ₂))
    [⊢][∧]-intro = [⊢]-construct
      (assumption-trees ↦ [∧]-intro
        (assumption-trees ([∈]-use))
        (assumption-trees ([∈]-skip [∈]-use))
      )

    [⊢][∧]-elimₗ : ∀{Γ}{φ₁ φ₂} → (((φ₁ ∧ φ₂) ⊰ Γ) ⊢ φ₁)
    [⊢][∧]-elimₗ = [⊢]-construct
      (assumption-trees ↦ [∧]-elimₗ
          (assumption-trees ([∈]-use))
      )

    [⊢][∧]-elimᵣ : ∀{Γ}{φ₁ φ₂} → (((φ₁ ∧ φ₂) ⊰ Γ) ⊢ φ₂)
    [⊢][∧]-elimᵣ = [⊢]-construct
      (assumption-trees ↦ [∧]-elimᵣ
        (assumption-trees ([∈]-use))
      )

    [⊢][∨]-introₗ : ∀{Γ}{φ₁ φ₂} → ((φ₁ ⊰ Γ) ⊢ (φ₁ ∨ φ₂))
    [⊢][∨]-introₗ = [⊢]-construct
      (assumption-trees ↦ [∨]-introₗ
        (assumption-trees ([∈]-use))
      )

    [⊢][∨]-introᵣ : ∀{Γ}{φ₁ φ₂} → ((φ₂ ⊰ Γ) ⊢ (φ₁ ∨ φ₂))
    [⊢][∨]-introᵣ = [⊢]-construct
      (assumption-trees ↦ [∨]-introᵣ
        (assumption-trees ([∈]-use))
      )

    [⊢][∨]-elim : ∀{Γ₁ Γ₂}{φ₁ φ₂ φ₃} → ((φ₁ ⊰ Γ₁) ⊢ φ₃) → ((φ₂ ⊰ Γ₂) ⊢ φ₃) → (((φ₁ ∨ φ₂) ⊰ (Γ₁ ++ Γ₂)) ⊢ φ₃)
    [⊢][∨]-elim {Γ₁}{Γ₂} ([⊢]-construct φ₁Γ⊢φ₃) ([⊢]-construct φ₂Γ⊢φ₃) = [⊢]-construct
      (assumption-trees ↦ [∨]-elim
        (assumption-trees ([∈]-use))
        (φ₁-tree ↦ (φ₁Γ⊢φ₃) (Trees.push (φ₁-tree) (Trees.[++]-left  {Γ₁}{Γ₂} (Trees.pop (\{γ} → assumption-trees {γ})))))
        (φ₂-tree ↦ (φ₂Γ⊢φ₃) (Trees.push (φ₂-tree) (Trees.[++]-right {Γ₁}{Γ₂} (Trees.pop (\{γ} → assumption-trees {γ})))))
      )

    [⊢][⇒]-intro : ∀{Γ}{φ₁ φ₂} → ((φ₁ ⊰ Γ) ⊢ φ₂) → (Γ ⊢ (φ₁ ⇒ φ₂))
    [⊢][⇒]-intro ([⊢]-construct φ₁Γ⊢φ₂) = [⊢]-construct
      (assumption-trees ↦ [⇒]-intro
        (φ-tree ↦ (φ₁Γ⊢φ₂) (Trees.push (φ-tree) (\{γ} → assumption-trees {γ})))
      )

    [⊢][⇒]-elim : ∀{Γ}{φ₁ φ₂} → (((φ₁ ⇒ φ₂) ⊰ φ₁ ⊰ Γ) ⊢ φ₂)
    [⊢][⇒]-elim = [⊢]-construct
      (assumption-trees ↦ [⇒]-elim
        (assumption-trees ([∈]-use))
        (assumption-trees ([∈]-skip [∈]-use))
      )

    [⊢]-rules : Meta.[⊢]-rules (_⊢_)
    [⊢]-rules =
      record{
        [⊤]-intro  = \{Γ} → [⊢][⊤]-intro {Γ} ;
        [⊥]-intro  = \{Γ}{φ} → [⊢][⊥]-intro {Γ}{φ} ;
        [⊥]-elim   = \{Γ}{φ} → [⊢][⊥]-elim {Γ}{φ} ;
        [¬]-intro  = \{Γ}{φ} → [⊢][¬]-intro {Γ}{φ} ;
        [¬]-elim   = \{Γ}{φ} → [⊢][¬]-elim {Γ}{φ} ;
        [∧]-intro  = \{Γ}{φ₁}{φ₂} → [⊢][∧]-intro {Γ}{φ₁}{φ₂} ;
        [∧]-elimₗ  = \{Γ}{φ₁}{φ₂} → [⊢][∧]-elimₗ {Γ}{φ₁}{φ₂} ;
        [∧]-elimᵣ  = \{Γ}{φ₁}{φ₂} → [⊢][∧]-elimᵣ {Γ}{φ₁}{φ₂} ;
        [∨]-introₗ = \{Γ}{φ₁}{φ₂} → [⊢][∨]-introₗ {Γ}{φ₁}{φ₂} ;
        [∨]-introᵣ = \{Γ}{φ₁}{φ₂} → [⊢][∨]-introᵣ {Γ}{φ₁}{φ₂} ;
        [∨]-elim   = \{Γ₁}{Γ₂}{φ₁ φ₂ φ₃} → [⊢][∨]-elim {Γ₁}{Γ₂}{φ₁}{φ₂}{φ₃} ;
        [⇒]-intro  = \{Γ}{φ₁}{φ₂} → [⊢][⇒]-intro {Γ}{φ₁}{φ₂} ;
        [⇒]-elim   = \{Γ}{φ₁}{φ₂} → [⊢][⇒]-elim {Γ}{φ₁}{φ₂}
      }

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
