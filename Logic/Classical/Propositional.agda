module Logic.Classical.Propositional {ℓ} where

open import Data
open import Functional
import      Logic.Propositional{ℓ} as Constructive
import      Logic.Propositional.Theorems{ℓ}      as ConstructiveTheorems
import      Lvl
open import Type

Stmt = Constructive.Stmt

-- Classical propositions are expressed as propositions wrapped in double negation.
-- TODO: I am not sure, but I think this works? My reasoning is the following:
-- • [¬¬]-elim ↔ excluded-middle
--     Double negation elimination is equivalent to excluded middle.
--     There are proofs of this.
-- • Theory(ClassicalLogic) = Theory(ConstructiveLogic ∪ {excludedMiddle})
--     Constructive logic is classical logic without EM.
--     EM is the difference between constructive and classical.
--     This seems to be a common description of constructive logic.
--     • Theory(ClassicalLogic) ⊈ Theory(ConstructiveLogic)
--     • Theory(ClassicalLogic) ⊇ Theory(ConstructiveLogic)
-- • [¬¬]-intro ∈ Theory(ConstructiveLogic)
--     Double negation introduction exists in constructive logic.
-- • (∀φ. ¬¬¬¬φ → ¬¬φ) ∈ Theory(ConstructiveLogic)
--     Double negation elimination exists inside a double negation in constructive logic.
-- • Every natural deduction introduction/elimination rule in constructive logic can be expressed inside a double negation.
-- Therefore:
-- • Theory(ClassicalLogic) = Theory(ConstructiveLogic ∪ {[¬¬]-elim}).
-- • The theory inside double negation in constructive logic is (at least) a classical logic.
--     Because every intro/elim rule exists in there,
--     the propositions inside a double negation are at least a constructive logic.
--     But [¬¬]-elim also exists in there.
--     Therefore it is at least a classical logic.
-- This cannot be done with predicate logic because the translation for [∀] does not hold in both directions.
Classic = Constructive.¬¬_

module Opers where
  infixl 1010 ¬_
  infixl 1005 _∧_
  infixl 1004 _∨_
  infixl 1000 _⟵_ _⟷_ _⟶_

  _∧_ : Stmt → Stmt → Stmt
  _∧_ X Y = Classic(Constructive._∧_ X Y)

  _⟶_ : Stmt → Stmt → Stmt
  _⟶_ A B = Classic(A → B)

  _⟵_ : Stmt → Stmt → Stmt
  _⟵_ A B = Classic(A ← B)

  _⟷_ : Stmt → Stmt → Stmt
  _⟷_ A B = Classic(Constructive._↔_ A B)

  _∨_ : Stmt → Stmt → Stmt
  _∨_ A B = Classic(Constructive._∨_ A B)

  ⊥ : Stmt
  ⊥ = Classic(Constructive.⊥)

  ⊤ : Stmt
  ⊤ = Classic(Constructive.⊤)

  ¬_ : Stmt → Stmt
  ¬_ A = Classic(Constructive.¬_ A)

module _ where
  open Constructive
    using(_∧_ ; _∨_ ; _↔_ ; ⊥ ; ⊤ ; ¬_ ; ¬¬_ )

  -- Also called: Double-negation shifts
  [¬¬][→]-preserving : ∀{X Y} → Classic(X → Y) ↔ (Classic(X) → Classic(Y))
  [¬¬][→]-preserving{X}{Y} = Constructive.[↔]-intro l r where
    open Constructive
    open ConstructiveTheorems

    l : Classic(X → Y) ← (Classic(X) → Classic(Y))
    l = [→]ᵣ-[¬¬]-move-out ∘ [→]ₗ-[¬¬]-elim

    r : Classic(X → Y) → (Classic(X) → Classic(Y))
    r(nnxy)(nnx)(ny) =
      (([→]-elim
        ((xy ↦
          (([→]-elim
            (([→]-elim
              (([⊥]-elim
                (([→]-elim
                  ((x ↦
                    (([→]-elim
                      (([→]-elim x xy) :of: Y)
                      (ny :of: (Y → ⊥))
                    ) :of: ⊥)
                  ) :of: (X → ⊥))
                  (nnx :of: ((X → ⊥) → ⊥))
                ) :of: ⊥)
              ) :of: X)
              (xy :of: (X → Y))
            ) :of: Y)
            (ny :of: (Y → ⊥))
          ) :of: ⊥)
        ) :of: ((X → Y) → ⊥))
        (nnxy :of: ¬¬(X → Y))
      ) :of: ⊥)

  ------------------------------------------
  -- Converting theorems with implication in constructive logic to classical logic

  prop-intro : ∀{X} → X → Classic(X)
  prop-intro = ConstructiveTheorems.[¬¬]-intro

  [→]₁-intro : ∀{X Y} → (X → Y) → (Classic(X) → Classic(Y))
  [→]₁-intro = ConstructiveTheorems.double-contrapositiveᵣ

  [→]₂-intro : ∀{X Y Z} → (X → Y → Z) → (Classic(X) → Classic(Y) → Classic(Z))
  [→]₂-intro(xyz) = (Constructive.[↔]-elimᵣ [¬¬][→]-preserving) ∘ ([→]₁-intro(xyz))

  [→]₃-intro : ∀{X Y Z W} → (X → Y → Z → W) → (Classic(X) → Classic(Y) → Classic(Z) → Classic(W))
  [→]₃-intro{X}{Y}{Z}{W}(xyzw) = (Constructive.[↔]-elimᵣ [¬¬][→]-preserving) ∘₂ ([→]₂-intro(xyzw))

  ------------------------------------------
  -- Conjunction (AND)

  [∧]-intro : ∀{X Y} → Classic(X) → Classic(Y) → Classic(X ∧ Y)
  [∧]-intro = [→]₂-intro(Constructive.[∧]-intro)

  [∧]-elimₗ : ∀{X Y} → Classic(X ∧ Y) → Classic(X)
  [∧]-elimₗ = [→]₁-intro(Constructive.[∧]-elimₗ)

  [∧]-elimᵣ : ∀{X Y} → Classic(X ∧ Y) → Classic(Y)
  [∧]-elimᵣ = [→]₁-intro(Constructive.[∧]-elimᵣ)

  ------------------------------------------
  -- Implication

  [→]-elim : ∀{X Y} → Classic(X) → Classic(X → Y) → Classic(Y)
  [→]-elim = [→]₂-intro(Constructive.[→]-elim)

  [→]-intro : ∀{X Y : Stmt} → Classic(Y) → Classic(X → Y)
  [→]-intro = [→]₁-intro(Constructive.[→]-intro)

  ------------------------------------------
  -- Reverse implication

  [←]-intro : ∀{X Y : Stmt} → Classic(Y) → Classic(Y ← X)
  [←]-intro = [→]₁-intro(Constructive.[←]-intro)

  [←]-elim : ∀{X Y} → Classic(X) → Classic(Y ← X) → Classic(Y)
  [←]-elim = [→]₂-intro(Constructive.[←]-elim)

  ------------------------------------------
  -- Equivalence

  [↔]-intro : ∀{X Y} → Classic(X ← Y) → Classic(X → Y) → Classic(X ↔ Y)
  [↔]-intro = [→]₂-intro(Constructive.[↔]-intro)

  [↔]-elimₗ : ∀{X Y} → Classic(X ↔ Y) → Classic(X ← Y)
  [↔]-elimₗ = [→]₁-intro(Constructive.[↔]-elimₗ)

  [↔]-elimᵣ : ∀{X Y} → Classic(X ↔ Y) → Classic(X → Y)
  [↔]-elimᵣ = [→]₁-intro(Constructive.[↔]-elimᵣ)

  ------------------------------------------
  -- Disjunction (OR)

  [∨]-introₗ : ∀{X Y} → Classic(X) → Classic(X ∨ Y)
  [∨]-introₗ = [→]₁-intro(Constructive.[∨]-introₗ)

  [∨]-introᵣ : ∀{X Y} → Classic(Y) → Classic(X ∨ Y)
  [∨]-introᵣ = [→]₁-intro(Constructive.[∨]-introᵣ)

  [∨]-elim : ∀{X Y Z} → Classic(X → Z) → Classic(Y → Z) → Classic(X ∨ Y) → Classic(Z)
  [∨]-elim = [→]₃-intro(Constructive.[∨]-elim)

  ------------------------------------------
  -- Bottom (false, absurdity, empty, contradiction)

  [⊥]-intro : ∀{X} → Classic(X) → Classic(X → ⊥) → Classic(⊥)
  [⊥]-intro = [→]₂-intro(Constructive.[⊥]-intro)

  [⊥]-elim : ∀{X} → Classic(⊥) → Classic(X)
  [⊥]-elim = [→]₁-intro(Constructive.[⊥]-elim)

  ------------------------------------------
  -- Top (true, truth, unit, validity)

  [⊤]-intro : Classic(⊤)
  [⊤]-intro = prop-intro(Constructive.[⊤]-intro)

  ------------------------------------------
  -- Negation

  [¬]-intro : ∀{X} → Classic(X → ⊥) → Classic(¬ X)
  [¬]-intro = [→]₁-intro(Constructive.[¬]-intro)

  [¬]-elim : ∀{X} → Classic(¬ X) → Classic(X → ⊥)
  [¬]-elim = [→]₁-intro(Constructive.[¬]-elim)

  ------------------------------------------
  -- For-all quantification

  -- [∀]-intro : ∀{P} → (∀{x} → Classic(P(x))) → Classic(∀{x} → P(x))
  -- [∀]-intro = [→]₁-intro(Constructive.[¬]-intro)
    -- (∀x. ¬¬P(x)) → (¬¬∀x. P(x))
    -- (∀x. ¬¬P(x)) → (¬¬∀x. P(x))

  -- postulate [∀]-elim : ∀{P} → Classic(∀{x} → P(x)) → ∀{x} → Classic(P(x))

  ------------------------------------------
  -- Theorems exclusive to classic logic (compared to constructive logic)

  [¬¬]-elim : ∀{X} → Classic(¬¬ X) → Classic(X)
  [¬¬]-elim = ConstructiveTheorems.[¬¬¬]-elim

  excluded-middle : ∀{X} → Classic(X ∨ (¬ X))
  excluded-middle{X} =
    (Constructive.[¬]-intro(naorna ↦
      ((ConstructiveTheorems.non-contradiction(Constructive.[∧]-intro
        ((Constructive.[∨]-introᵣ
          ((Constructive.[¬]-intro(a ↦
            ((ConstructiveTheorems.non-contradiction(Constructive.[∧]-intro
              ((Constructive.[∨]-introₗ a) :of:  (X ∨ (¬ X)))
              (naorna                      :of: ¬(X ∨ (¬ X)))
            )) :of: ⊥)
          )) :of: (¬ X))
        ) :of: (X ∨ (¬ X)))
        (naorna :of: ¬(X ∨ (¬ X)))
      )) :of: ⊥)
    )) :of: ¬¬(X ∨ (¬ X))

  [¬]-elim₂ : ∀{X} → Classic((¬ X) → ⊥) → Classic(X)
  [¬]-elim₂ = [¬¬]-elim ∘ [¬]-intro

  postulate contrapositiveₗ : ∀{X Y : Stmt} → Classic(X → Y) ← Classic((¬ X) ← (¬ Y))

  double-contrapositiveₗ : ∀{X Y : Stmt} → Classic(X → Y) ← Classic((¬¬ X) → (¬¬ Y))
  double-contrapositiveₗ = contrapositiveₗ ∘ contrapositiveₗ

  ------------------------------------------
  -- Theorems

  [→][∧]-assumptionₗ : {X Y Z : Stmt} → Classic((X ∧ Y) → Z) ← Classic(X → Y → Z)
  [→][∧]-assumptionₗ = [→]₁-intro(Tuple.uncurry)

  [→][∧]-assumptionᵣ : {X Y Z : Stmt} → Classic((X ∧ Y) → Z) → Classic(X → Y → Z)
  [→][∧]-assumptionᵣ = [→]₁-intro(Tuple.curry)

  [¬¬]-intro : ∀{X} → Classic(X) → Classic(¬¬ X)
  [¬¬]-intro = ConstructiveTheorems.[¬¬]-intro

  double-contrapositiveᵣ : ∀{X Y} → Classic(X → Y) → Classic(¬¬ X → ¬¬ Y)
  double-contrapositiveᵣ = [→]₁-intro [→]₁-intro
