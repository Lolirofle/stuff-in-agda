module Metalogic.Classical.Propositional.ProofSystem {ℓₚ} (Proposition : Set(ℓₚ)) where

import      Lvl
open import Data hiding (empty)
import      Data.List
open        Data.List using (List ; ∅ ; _⊰_ ; _++_ ; [_ ; _])
open        Data.List.Notation
import      Data.List.Relation.Membership
import      Data.List.Relation.Membership.Proofs
open import Metalogic.Classical.Propositional.Syntax(Proposition)
open import Functional

open        Data.List.Relation.Membership{ℓₚ} {Formula}
open        Data.List.Relation.Membership.Proofs{ℓₚ} {Formula}

module Meta where
  data _⊢_ : List(Formula) → Formula → Set(ℓₚ) where -- TODO: Reduce the number of rules
    [⊤]-intro : ∀{Γ} → (Γ ⊢ ⊤)

    [⊥]-intro : ∀{Γ}{φ} → (φ ∈ Γ) → ((¬ φ) ∈ Γ) → (Γ ⊢ ⊥)
    [⊥]-elim  : ∀{Γ}{φ} → (⊥ ∈ Γ) → (Γ ⊢ φ)

    [¬]-intro : ∀{Γ}{φ} → ((φ ∈ Γ) → (Γ ⊢ ⊥)) → (Γ ⊢ (¬ φ))
    [¬]-elim  : ∀{Γ}{φ} → (((¬ φ) ∈ Γ) → (Γ ⊢ ⊥)) → (Γ ⊢ φ)

    [∧]-intro : ∀{Γ}{φ₁ φ₂} → (φ₁ ∈ Γ) → (φ₂ ∈ Γ) → (Γ ⊢ (φ₁ ∧ φ₂))
    [∧]-elimₗ  : ∀{Γ}{φ₁ φ₂} → ((φ₁ ∧ φ₂) ∈ Γ) → (Γ ⊢ φ₁)
    [∧]-elimᵣ  : ∀{Γ}{φ₁ φ₂} → ((φ₁ ∧ φ₂) ∈ Γ) → (Γ ⊢ φ₂)

    [∨]-introₗ : ∀{Γ}{φ₁ φ₂} → (φ₁ ∈ Γ) → (Γ ⊢ (φ₁ ∨ φ₂))
    [∨]-introᵣ : ∀{Γ}{φ₁ φ₂} → (φ₂ ∈ Γ) → (Γ ⊢ (φ₁ ∨ φ₂))
    [∨]-elim   : ∀{Γ}{φ₁ φ₂ φ₃} → ((φ₁ ∈ Γ) → (Γ ⊢ φ₃)) → ((φ₂ ∈ Γ) → (Γ ⊢ φ₃)) → ((φ₁ ∨ φ₂) ∈ Γ) → (Γ ⊢ φ₃)

    [⇒]-intro : ∀{Γ}{φ₁ φ₂} → ((φ₁ ∈ Γ) → (Γ ⊢ φ₂)) → (Γ ⊢ (φ₁ ⇒ φ₂))
    [⇒]-elim  : ∀{Γ}{φ₁ φ₂} → ((φ₁ ⇒ φ₂) ∈ Γ) → (φ₁ ∈ Γ) → (Γ ⊢ φ₂)

  [¬¬]-elim : ∀{Γ}{φ} → ((¬ ¬ φ) ∈ Γ) → (Γ ⊢ φ)
  [¬¬]-elim{Γ}{φ} ([¬¬φ]-in) =
    ([¬]-elim{Γ}{φ} ([¬φ]-in ↦
      ([⊥]-intro{Γ}{¬ φ}
        ([¬φ]-in)
        ([¬¬φ]-in)
      )
    ))

  _⊬_ : List(Formula) → Formula → Set(ℓₚ)
  _⊬_ Γ φ = (_⊢_ Γ φ) → Empty{ℓₚ}

  -- Consistency
  Inconsistent : List(Formula) → Set(ℓₚ)
  Inconsistent Γ = (Γ ⊢ ⊥)

  Consistent : List(Formula) → Set(ℓₚ)
  Consistent Γ = (Γ ⊬ ⊥)

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
  {-# NO_POSITIVITY_CHECK #-} -- TODO: Could this be a problem? Maybe not? Classical logic is supposed to be consistent, but maybe that does not have anything to do with this?
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
    [∨]-elim  : ∀{φ₁ φ₂ φ₃} → (Tree(φ₁) → Tree(φ₃)) → (Tree(φ₂) → Tree(φ₃)) → Tree(φ₁ ∨ φ₂) → Tree(φ₃)

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
  -- Trees(Γ) is the statement that all formulas in Γ have proof trees.
  Trees : List(Formula) → Set(ℓₚ)
  Trees(Γ) = (∀{γ} → (γ ∈ Γ) → Tree(γ))

  module Trees where
    tree : ∀{Γ}{φ} → Trees(Γ) → (φ ∈ Γ) → Tree(φ)
    tree f(x) = f(x)

    empty : Trees(∅)
    empty ()

    singleton : ∀{φ} → Tree(φ) → Trees([ φ ])
    singleton (φ-tree) (use) = φ-tree
    singleton (φ-tree) (skip ())

    -- TODO: This could possibly be generalized to: ∀{Γ₁ Γ₂}{F : T → Set} → (∀{a} → (a ∈ Γ₁) → (a ∈ Γ₂)) → ((∀{γ} → (γ ∈ Γ₂) → F(γ)) → (∀{γ} → (γ ∈ Γ₁) → F(γ)))
    from-[∈] : ∀{Γ₁ Γ₂} → (∀{a} → (a ∈ Γ₁) → (a ∈ Γ₂)) → (Trees(Γ₂) → Trees(Γ₁))
    from-[∈] (f) (Γ₂-trees) {γ} = liftᵣ (f{γ}) (Γ₂-trees)

    push : ∀{Γ}{φ} → Tree(φ) → Trees(Γ) → Trees(φ ⊰ Γ)
    push (φ-tree) (Γ-tree) (use) = φ-tree
    push (φ-tree) (Γ-tree) (skip membership) = Γ-tree (membership)

    pop : ∀{Γ}{φ} → Trees(φ ⊰ Γ) → Trees(Γ)
    pop = from-[∈] (skip)

    first : ∀{Γ}{φ} → Trees(φ ⊰ Γ) → Tree(φ)
    first(f) = f(use)

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
    [++]-deduplicate {Γ} (trees) {γ} = liftᵣ([∈][++]-expandₗ {γ}{Γ}{Γ})(trees{γ})

    [⊰]-reorderₗ : ∀{Γ₁ Γ₂}{φ} → Trees(Γ₁ ++ (φ ⊰ Γ₂)) → Trees(φ ⊰ (Γ₁ ++ Γ₂))
    [⊰]-reorderₗ {Γ₁}{Γ₂}{φ} (Γ₁φΓ₂-trees) = push (φ-tree) ([++]-commute{Γ₂}{Γ₁} Γ₂Γ₁-trees) where
      φΓ₂Γ₁-trees : Trees(φ ⊰ (Γ₂ ++ Γ₁))
      φΓ₂Γ₁-trees = [++]-commute{Γ₁}{φ ⊰ Γ₂} (Γ₁φΓ₂-trees)

      φ-tree : Tree(φ)
      φ-tree = first{Γ₂ ++ Γ₁}{φ} (φΓ₂Γ₁-trees)

      Γ₂Γ₁-trees : Trees(Γ₂ ++ Γ₁)
      Γ₂Γ₁-trees = pop{Γ₂ ++ Γ₁}{φ} (φΓ₂Γ₁-trees)
    -- Γ₁ ++ (φ ⊰ Γ₂) //assumption
    -- (φ ⊰ Γ₂) ++ Γ₁ //Trees.[++]-commute
    -- φ ⊰ (Γ₂ ++ Γ₁) //Definition: (++)
    -- φ ⊰ (Γ₁ ++ Γ₂) //Trees.[++]-commute

    push-many : ∀{Γ₁ Γ₂} → Trees(Γ₁) → Trees(Γ₂) → Trees(Γ₁ ++ Γ₂)
    push-many{∅}     {Γ₂} ([∅]-trees)    ([Γ₂]-trees) = [Γ₂]-trees
    push-many{φ ⊰ Γ₁}{Γ₂} ([φ⊰Γ₁]-trees) ([Γ₂]-trees) = [⊰]-reorderₗ{Γ₁}{Γ₂}{φ} (push-many{Γ₁}{φ ⊰ Γ₂} (pop [φ⊰Γ₁]-trees) (push (first [φ⊰Γ₁]-trees) [Γ₂]-trees))

  -- Derivability
  -- Proof of: If there exists a tree for every formula in Γ, then there exists a tree for the formula φ.
  data _⊢_ (Γ : List(Formula)) (φ : Formula) : Set(ℓₚ) where
    [⊢]-construct : (Trees(Γ) → Tree(φ)) → (Γ ⊢ φ)

  module Theorems where
    [⊢]-from-trees : ∀{Γ₁ Γ₂}{φ} → (Trees(Γ₂) → Trees(Γ₁)) → (Γ₁ ⊢ φ) → (Γ₂ ⊢ φ)
    [⊢]-from-trees (trees-fn) ([⊢]-construct (Γ₁⊢φ)) = [⊢]-construct ((Γ₁⊢φ) ∘ (trees-fn))

    [⊢]-formula-weaken : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ φ₁) → ((φ₂ ⊰ Γ) ⊢ φ₁)
    [⊢]-formula-weaken {_}{_}{φ₂} = [⊢]-from-trees (Trees.pop {_}{φ₂})

    [⊢]-weakenₗ : ∀{Γ₂}{φ} → (Γ₂ ⊢ φ) → ∀{Γ₁} → ((Γ₁ ++ Γ₂) ⊢ φ)
    [⊢]-weakenₗ {_} {_} (Γ₂⊢φ) {∅}       = (Γ₂⊢φ)
    [⊢]-weakenₗ {Γ₂}{φ} (Γ₂⊢φ) {φ₂ ⊰ Γ₁} = [⊢]-formula-weaken {Γ₁ ++ Γ₂} ([⊢]-weakenₗ (Γ₂⊢φ) {Γ₁})

    [⊢]-reorder-[++] : ∀{Γ₁ Γ₂}{φ} → ((Γ₁ ++ Γ₂) ⊢ φ) → ((Γ₂ ++ Γ₁) ⊢ φ)
    [⊢]-reorder-[++] {Γ₁}{Γ₂} = [⊢]-from-trees (Trees.[++]-commute {Γ₂}{Γ₁})

    [⊢]-apply : ∀{Γ}{φ} → (Γ ⊢ φ) → Trees(Γ) → Tree(φ)
    [⊢]-apply ([⊢]-construct [Γ]⊢[φ]) (Γ-trees) = ([Γ]⊢[φ]) (Γ-trees)

    [⊢]-apply-first : ∀{Γ}{φ₁ φ₂} → Tree(φ₁) → ((φ₁ ⊰ Γ) ⊢ φ₂) → (Γ ⊢ φ₂)
    [⊢]-apply-first ([φ₁]-tree) ([⊢]-construct ([φ₁⊰Γ]⊢[φ₂])) =
      [⊢]-construct([Γ]⊢[φ₂] ↦
        ([φ₁⊰Γ]⊢[φ₂]) (Trees.push ([φ₁]-tree) (\{γ} → [Γ]⊢[φ₂] {γ}))
      )

    [⊢]-apply-many : ∀{Γ₁ Γ₂}{φ} → Trees(Γ₁) → ((Γ₁ ++ Γ₂) ⊢ φ) → (Γ₂ ⊢ φ)
    [⊢]-apply-many ([Γ₁]-trees) ([⊢]-construct ([Γ₁++Γ₂]⊢[φ])) =
      [⊢]-construct([Γ₂]⊢[φ] ↦
        ([Γ₁++Γ₂]⊢[φ]) (Trees.push-many ([Γ₁]-trees) (\{γ} → [Γ₂]⊢[φ] {γ}))
      )

    [⊢]-reorderᵣ-[⊰] : ∀{Γ₁ Γ₂}{φ₁ φ₂} → ((Γ₁ ++ (φ₁ ⊰ Γ₂)) ⊢ φ₂) ← ((φ₁ ⊰ (Γ₁ ++ Γ₂)) ⊢ φ₂)
    [⊢]-reorderᵣ-[⊰] {Γ₁}{Γ₂}{φ₁} = [⊢]-from-trees (Trees.[⊰]-reorderₗ {Γ₁}{Γ₂}{φ₁})

    [⊢]-id : ∀{Γ}{φ} → (φ ∈ Γ) → (Γ ⊢ φ)
    [⊢]-id (φ-in) = [⊢]-construct ([∈]-proof ↦ [∈]-proof (φ-in))
    -- ((A → B) → B) → C
    -- f(g ↦ g(x))

    -- Almost like that cut rule.
    [⊢]-compose : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ φ₁) → ((φ₁ ⊰ Γ) ⊢ φ₂) → (Γ ⊢ φ₂)
    [⊢]-compose ([Γ]⊢[φ₁]) ([φ₁Γ]⊢[φ₂]) =
      [⊢]-construct ([Γ]-trees ↦
        let [φ₁]-tree = [⊢]-apply ([Γ]⊢[φ₁]) (\{γ} → [Γ]-trees {γ})
            [Γ]⊢[φ₂]  = [⊢]-apply-first ([φ₁]-tree) ([φ₁Γ]⊢[φ₂])
        in [⊢]-apply ([Γ]⊢[φ₂]) (\{γ} → [Γ]-trees {γ})
      )
    -- TODO: ∀{Γ}{φ₁ φ₂} → (Γ ⊢ φ₁) → ((φ₁ ∈ Γ) → (Γ ⊢ φ₂)) → (Γ ⊢ φ₂) Provable?

    [⊢]-membership-precedingₗ : ∀{Γ}{φ₁ φ₂} → ((φ₁ ∈ Γ) → (Γ ⊢ φ₂)) ← ((φ₁ ⊰ Γ) ⊢ φ₂)
    [⊢]-membership-precedingₗ{Γ}{φ₁}{φ₂} ([φ₁Γ]⊢[φ₂]) ([φ₁]-in) =
      [⊢]-construct([Γ]-trees ↦
        [⊢]-apply ([φ₁Γ]⊢[φ₂]) (Trees.push ([Γ]-trees [φ₁]-in) (\{γ} → [Γ]-trees {γ}))
      )

    {- TODO: Maybe this is unprovable? And also false?
    postulate a : ∀{b : Set(ℓₚ)} → b
    [⊢]-membership-precedingᵣ : ∀{Γ}{φ₁ φ₂} → ((φ₁ ∈ Γ) → (Γ ⊢ φ₂)) → ((φ₁ ⊰ Γ) ⊢ φ₂)
    [⊢]-membership-precedingᵣ{Γ}{φ₁}{φ₂} (incl) =
      [⊢]-construct ([φ₁Γ]-trees ↦
        let [Γ]-trees = Trees.pop (\{γ} → [φ₁Γ]-trees {γ})
            [φ₁]-in = a
            [Γ]⊢[φ₂] = incl([φ₁]-in)
        in [⊢]-apply ([Γ]⊢[φ₂]) ([Γ]-trees)
      )
    -}

    [⊢][⊤]-intro : ∀{Γ} → (Γ ⊢ ⊤)
    [⊢][⊤]-intro =
      [⊢]-construct(const [⊤]-intro)

    [⊢][⊥]-intro : ∀{Γ}{φ} → (φ ∈ Γ) → ((¬ φ) ∈ Γ) → (Γ ⊢ ⊥)
    [⊢][⊥]-intro ([φ]-in) ([¬φ]-in) =
      [⊢]-construct(assumption-trees ↦
        ([⊥]-intro
          (assumption-trees ([φ]-in))
          (assumption-trees ([¬φ]-in))
        )
      )

    [⊢][⊥]-elim : ∀{Γ}{φ} → (⊥ ∈ Γ) → (Γ ⊢ φ)
    [⊢][⊥]-elim ([⊥]-in) =
      [⊢]-construct(assumption-trees ↦
        ([⊥]-elim
          (assumption-trees ([⊥]-in))
        )
      )

    [⊢][¬]-intro : ∀{Γ}{φ} → ((φ ⊰ Γ) ⊢ ⊥) → (Γ ⊢ (¬ φ))
    [⊢][¬]-intro ([⊢]-construct φΓ⊢⊥) =
      [⊢]-construct(assumption-trees ↦
        ([¬]-intro (φ-tree ↦
          (φΓ⊢⊥) (Trees.push (φ-tree) (\{γ} → assumption-trees {γ}))
        ))
      )

    [⊢][¬]-elim : ∀{Γ}{φ} → (((¬ φ) ⊰ Γ) ⊢ ⊥) → (Γ ⊢ φ)
    [⊢][¬]-elim ([⊢]-construct ¬φΓ⊢⊥) =
      [⊢]-construct(assumption-trees ↦
        ([¬]-elim (φ-tree ↦
          (¬φΓ⊢⊥) (Trees.push (φ-tree) (\{γ} → assumption-trees {γ}))
        ))
      )

    [⊢][∧]-intro : ∀{Γ}{φ₁ φ₂} → (φ₁ ∈ Γ) → (φ₂ ∈ Γ) → (Γ ⊢ (φ₁ ∧ φ₂))
    [⊢][∧]-intro ([φ₁]-in) ([φ₂]-in) =
      [⊢]-construct(assumption-trees ↦
        ([∧]-intro
          (assumption-trees ([φ₁]-in))
          (assumption-trees ([φ₂]-in))
        )
      )

    [⊢][∧]-elimₗ : ∀{Γ}{φ₁ φ₂} → ((φ₁ ∧ φ₂) ∈ Γ) → (Γ ⊢ φ₁)
    [⊢][∧]-elimₗ ([φ₁∧φ₂]-in) =
      [⊢]-construct(assumption-trees ↦
        [∧]-elimₗ (assumption-trees ([φ₁∧φ₂]-in))
      )

    [⊢][∧]-elimᵣ : ∀{Γ}{φ₁ φ₂} → ((φ₁ ∧ φ₂) ∈ Γ) → (Γ ⊢ φ₂)
    [⊢][∧]-elimᵣ ([φ₁∧φ₂]-in) =
      [⊢]-construct(assumption-trees ↦
        [∧]-elimᵣ (assumption-trees ([φ₁∧φ₂]-in))
      )

    [⊢][∨]-introₗ : ∀{Γ}{φ₁ φ₂} → (φ₁ ∈ Γ) → (Γ ⊢ (φ₁ ∨ φ₂))
    [⊢][∨]-introₗ ([φ₁]-in) =
      [⊢]-construct(assumption-trees ↦
        [∨]-introₗ (assumption-trees ([φ₁]-in))
      )

    [⊢][∨]-introᵣ : ∀{Γ}{φ₁ φ₂} → (φ₂ ∈ Γ) → (Γ ⊢ (φ₁ ∨ φ₂))
    [⊢][∨]-introᵣ ([φ₂]-in) =
      [⊢]-construct(assumption-trees ↦
        [∨]-introᵣ (assumption-trees ([φ₂]-in))
      )

    [⊢][∨]-elim : ∀{Γ₁ Γ₂}{φ₁ φ₂ φ₃} → ((φ₁ ⊰ Γ₁) ⊢ φ₃) → ((φ₂ ⊰ Γ₂) ⊢ φ₃) → (((φ₁ ∨ φ₂) ⊰ (Γ₁ ++ Γ₂)) ⊢ φ₃)
    [⊢][∨]-elim {Γ₁}{Γ₂} ([⊢]-construct φ₁Γ⊢φ₃) ([⊢]-construct φ₂Γ⊢φ₃) = [⊢]-construct
      (assumption-trees ↦ [∨]-elim
        (φ₁-tree ↦ (φ₁Γ⊢φ₃) (Trees.push (φ₁-tree) (Trees.[++]-left  {Γ₁}{Γ₂} (Trees.pop (\{γ} → assumption-trees {γ})))))
        (φ₂-tree ↦ (φ₂Γ⊢φ₃) (Trees.push (φ₂-tree) (Trees.[++]-right {Γ₁}{Γ₂} (Trees.pop (\{γ} → assumption-trees {γ})))))
        (assumption-trees (use))
      )

    [⊢][⇒]-intro : ∀{Γ}{φ₁ φ₂} → ((φ₁ ⊰ Γ) ⊢ φ₂) → (Γ ⊢ (φ₁ ⇒ φ₂))
    [⊢][⇒]-intro ([⊢]-construct φ₁Γ⊢φ₂) = [⊢]-construct
      (assumption-trees ↦ [⇒]-intro
        (φ-tree ↦ (φ₁Γ⊢φ₂) (Trees.push (φ-tree) (\{γ} → assumption-trees {γ})))
      )

    [⊢][⇒]-elim : ∀{Γ}{φ₁ φ₂} → ((φ₁ ⇒ φ₂) ∈ Γ) → (φ₁ ∈ Γ) → (Γ ⊢ φ₂)
    [⊢][⇒]-elim ([φ₁⇒φ₂]-in) ([φ₁]-in) =
      [⊢]-construct(assumption-trees ↦
        [⇒]-elim
          (assumption-trees ([φ₁⇒φ₂]-in))
          (assumption-trees ([φ₁]-in))
      )

    -- [⊢]-metaᵣ : ∀{a}{b} → _⊢_ a b → Meta._⊢_ a b
    -- [⊢]-metaₗ : ∀{a}{b} → _⊢_ a b ← Meta._⊢_ a b

    {-[⊢]-rules : Meta.[⊢]-rules (_⊢_)
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
    -}
