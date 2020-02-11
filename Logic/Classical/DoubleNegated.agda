module Logic.Classical.DoubleNegated where

open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic
import      Lvl
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable X Y Z W : Stmt{ℓ}
private variable P : X → Stmt{ℓ}

module _ where
  open import Logic.Propositional
  open import Logic.Propositional.Theorems

  [→]ₗ-[¬¬]-elim : ((¬¬ X) → Y) → (X → Y)
  [→]ₗ-[¬¬]-elim = liftᵣ([¬¬]-intro)

  [→]ᵣ-[¬¬]-move-out : (X → (¬¬ Y)) → ¬¬(X → Y)
  [→]ᵣ-[¬¬]-move-out {X = X}{Y = Y} (xnny) =
    (nxy ↦
      ([→]-elim
        ((x ↦
          (([⊥]-elim
            (([→]-elim
              ((y ↦
                (([→]-elim
                  ((const y) :of: (X → Y))
                  (nxy           :of: ¬(X → Y))
                ) :of: ⊥)
              ) :of: (¬ Y))
              (([→]-elim x xnny) :of: (¬¬ Y))
            ) :of: ⊥)
          ) :of: Y)
        ) :of: (X → Y))
        (nxy :of: ¬(X → Y))
      )
    )

  double-contrapositiveᵣ : (X → Y) → ((¬¬ X) → (¬¬ Y)) -- Classic(X → Y) → Classic(¬¬ X → ¬¬ Y)
  double-contrapositiveᵣ = contrapositiveᵣ ∘ contrapositiveᵣ

  [¬¬]-double-contrapositiveₗ : ¬¬(X → Y) ← ((¬¬ X) → (¬¬ Y))
  [¬¬]-double-contrapositiveₗ {X = X}{Y = Y} p = [→]ᵣ-[¬¬]-move-out {X = X}{Y = Y} ([→]ₗ-[¬¬]-elim {X = X}{Y = ¬¬ Y} p)

module Propositional where
  import      Logic.Propositional          as Constructive
  import      Logic.Propositional.Theorems as ConstructiveTheorems
  import      Logic.Predicate              as Constructive1

  -- Classical propositions are expressed as propositions wrapped in double negation.
  -- TODO: I am not sure, but I think this works? My reasoning is the following:
  -- • [¬¬]-elim ↔ excluded-middle
  --     Double negation elimination is equivalent to excluded middle in constructive logic.
  -- • Theory(ClassicalLogic) = Theory(ConstructiveLogic ∪ {excludedMiddle})
  --     Constructive logic is classical logic without EM.
  --     EM is the difference between classical and constructive.
  --     • Theory(ClassicalLogic) ⊈ Theory(ConstructiveLogic)
  --     • Theory(ClassicalLogic) ⊇ Theory(ConstructiveLogic)
  --     This seems to be a common description of constructive logic.
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

    _∧_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
    _∧_ X Y = Classic(Constructive._∧_ X Y)

    _⟶_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
    _⟶_ A B = Classic(A → B)

    _⟵_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
    _⟵_ A B = Classic(A ← B)

    _⟷_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
    _⟷_ A B = Classic(Constructive._↔_ A B)

    _∨_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
    _∨_ A B = Classic(Constructive._∨_ A B)

    ⊥ : Stmt
    ⊥ = Classic(Constructive.⊥)

    ⊤ : Stmt
    ⊤ = Classic(Constructive.⊤)

    ¬_ : Stmt{ℓ} → Stmt
    ¬_ A = Classic(Constructive.¬_ A)

    ∀ₗ : (X → Stmt{ℓ}) → Stmt
    ∀ₗ P = Classic(Constructive1.∀ₗ P)

    ∃ : (X → Stmt{ℓ}) → Stmt
    ∃ P = Classic(Constructive1.∃ P)

  module _ where
    open Constructive
      using(_∧_ ; _∨_ ; _↔_ ; ⊥ ; ⊤ ; ¬_ ; ¬¬_ )
    open Constructive1 -- TODO: Should be somewhere else. This is the "Propositional" module
      using(∀ₗ ; ∃)

    -- Also called: Double-negation shifts
    [¬¬][→]-preserving : Classic(X → Y) ↔ (Classic(X) → Classic(Y))
    [¬¬][→]-preserving{X = X}{Y = Y} = Constructive.[↔]-intro l r where
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

    prop-intro : X → Classic(X)
    prop-intro = ConstructiveTheorems.[¬¬]-intro

    [→]₁-intro : (X → Y) → (Classic(X) → Classic(Y))
    [→]₁-intro = double-contrapositiveᵣ

    [→]₂-intro : (X → Y → Z) → (Classic(X) → Classic(Y) → Classic(Z))
    [→]₂-intro(xyz) = (Constructive.[↔]-to-[→] [¬¬][→]-preserving) ∘ ([→]₁-intro(xyz))

    [→]₃-intro : (X → Y → Z → W) → (Classic(X) → Classic(Y) → Classic(Z) → Classic(W))
    [→]₃-intro(xyzw) = (Constructive.[↔]-to-[→] [¬¬][→]-preserving) ∘₂ ([→]₂-intro(xyzw))

    ------------------------------------------
    -- Theorems

    [→][∧]-assumptionₗ : Classic((X ∧ Y) → Z) ← Classic(X → Y → Z)
    [→][∧]-assumptionₗ = [→]₁-intro(Tuple.uncurry)

    [→][∧]-assumptionᵣ : Classic((X ∧ Y) → Z) → Classic(X → Y → Z)
    [→][∧]-assumptionᵣ = [→]₁-intro(Tuple.curry)

    [¬¬]-intro : Classic(X) → Classic(¬¬ X)
    [¬¬]-intro = ConstructiveTheorems.[¬¬]-intro

    ------------------------------------------
    -- Conjunction (AND)

    [∧]-intro : Classic(X) → Classic(Y) → Classic(X ∧ Y)
    [∧]-intro = [→]₂-intro(Constructive.[∧]-intro)

    [∧]-elimₗ : Classic(X ∧ Y) → Classic(X)
    [∧]-elimₗ = [→]₁-intro(Constructive.[∧]-elimₗ)

    [∧]-elimᵣ : Classic(X ∧ Y) → Classic(Y)
    [∧]-elimᵣ = [→]₁-intro(Constructive.[∧]-elimᵣ)

    ------------------------------------------
    -- Implication

    [→]-elim : Classic(X → Y) → Classic(X) → Classic(Y)
    [→]-elim = [→]₂-intro(swap Constructive.[→]-elim)

    [→]-intro : (Classic(X) → Classic(Y)) → Classic(X → Y)
    [→]-intro = [¬¬]-double-contrapositiveₗ

    ------------------------------------------
    -- Reverse implication

    [←]-intro : (Classic(Y) ← Classic(X)) → Classic(Y ← X)
    [←]-intro = [¬¬]-double-contrapositiveₗ

    [←]-elim : Classic(X) → Classic(Y ← X) → Classic(Y)
    [←]-elim = [→]₂-intro(Constructive.[←]-elim)

    ------------------------------------------
    -- Equivalence

    [↔]-intro : (Classic(X) ← Classic(Y)) → (Classic(X) → Classic(Y)) → Classic(X ↔ Y)
    [↔]-intro yx xy = ([→]₂-intro(Constructive.[↔]-intro)) ([→]-intro yx) ([→]-intro xy)

    [↔]-elimₗ : Classic(X ↔ Y) → Classic(X) ← Classic(Y)
    [↔]-elimₗ = [→]-elim ∘ ([→]₁-intro(Constructive.[↔]-to-[←]))

    [↔]-elimᵣ : Classic(X ↔ Y) → Classic(X) → Classic(Y)
    [↔]-elimᵣ = [→]-elim ∘ ([→]₁-intro(Constructive.[↔]-to-[→]))

    ------------------------------------------
    -- Disjunction (OR)

    [∨]-introₗ : Classic(X) → Classic(X ∨ Y)
    [∨]-introₗ = [→]₁-intro(Constructive.[∨]-introₗ)

    [∨]-introᵣ : Classic(Y) → Classic(X ∨ Y)
    [∨]-introᵣ = [→]₁-intro(Constructive.[∨]-introᵣ)

    [∨]-elim : (Classic(X) → Classic(Z)) → (Classic(Y) → Classic(Z)) → Classic(X ∨ Y) → Classic(Z)
    [∨]-elim xz yz = ([→]₃-intro(Constructive.[∨]-elim)) ([→]-intro xz) ([→]-intro yz)

    ------------------------------------------
    -- Bottom (false, absurdity, empty, contradiction)

    [⊥]-intro : Classic(X) → Classic(¬ X) → Classic(⊥)
    [⊥]-intro = [→]₂-intro(Constructive.[⊥]-intro)

    [⊥]-elim : Classic(⊥) → Classic(X)
    [⊥]-elim = [→]₁-intro(Constructive.[⊥]-elim)

    ------------------------------------------
    -- Top (true, truth, unit, validity)

    [⊤]-intro : Classic(⊤)
    [⊤]-intro = prop-intro(Constructive.[⊤]-intro)

    ------------------------------------------
    -- Negation

    [¬]-intro : (Classic(X) → Classic(⊥)) → Classic(¬ X)
    [¬]-intro = ([→]₁-intro(Constructive.[¬]-intro)) ∘ [→]-intro

    [¬]-elim : Classic(¬ X) → Classic(X → ⊥)
    [¬]-elim = [→]₁-intro(Constructive.[¬]-elim)

    ------------------------------------------
    -- For-all quantification

    -- [∀]-intro : ∀{P} → (∀{x} → Classic(P(x))) → Classic(∀{x} → P(x))
    -- [∀]-intro (f) (g) = ConstructiveTheorems.[→]ᵣ-[¬¬]-move-out (f) (g)

    -- postulate [∀]-elim : ∀{P} → Classic(∀{x} → P(x)) → ∀{x} → Classic(P(x))
    -- TODO: [→]ₗ-[¬¬]-elim

    ------------------------------------------
    -- Existential quantification

    [∃]-intro : ∀{x} → Classic(P(x)) → Classic(∃ P)
    [∃]-intro {x = x} = [→]₁-intro(proof ↦ Constructive1.[∃]-intro (x) ⦃ proof ⦄)

    ------------------------------------------
    -- Theorems exclusive to classic logic (compared to constructive logic)

    [¬¬]-elim : Classic(¬¬ X) → Classic(X)
    [¬¬]-elim = ConstructiveTheorems.[¬¬¬]-elim

    excluded-middle : Classic(X ∨ (¬ X))
    excluded-middle{X = X} = ConstructiveTheorems.[¬¬]-excluded-middle

    [¬]-elim₂ : Classic((¬ X) → ⊥) → Classic(X)
    [¬]-elim₂ = [¬¬]-elim ∘ [¬]-intro ∘ [→]-elim

    [→]-disjunctive-formᵣ : Classic(X → Y) → Classic((¬ X) ∨ Y)
    [→]-disjunctive-formᵣ n-n-x→y n-nx∨y = (n-nx∨y ∘ Constructive.[∨]-introₗ) (n-n-x→y ∘ (n-nx∨y ∘ Constructive.[∨]-introᵣ ∘₂ apply))

    contrapositiveₗ : Classic(X → Y) ← Classic((¬ X) ← (¬ Y))
    contrapositiveₗ n-n-ny→nx = [→]-intro ([¬¬]-elim ∘ ConstructiveTheorems.contrapositiveᵣ([→]-elim n-n-ny→nx) ∘ [¬¬]-intro)

    double-contrapositiveₗ : Classic(X → Y) ← Classic((¬¬ X) → (¬¬ Y))
    double-contrapositiveₗ = contrapositiveₗ ∘ contrapositiveₗ

    postulate callcc : Classic(((X → Y) → X) → X)
    {-callcc =
      ([→]-intro(xyx ↦
        ([→]-disjunctive-formᵣ
        )
      ))
    -}

    -- postulate callcc2 : ∀{X Y Z} → ((X → Y) → Z) → X

module _ where
  open import Logic.Propositional
  open import Logic.Propositional.Theorems

  [weak-excluded-middle]-to-[[¬][∧]ₗ] : (∀{ℓ}{P : Stmt{ℓ}} → (¬ P) ∨ (¬¬ P)) → (∀{ℓ₁ ℓ₂}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → ((¬ P) ∨ (¬ Q)) ← (¬ (P ∧ Q)))
  [weak-excluded-middle]-to-[[¬][∧]ₗ] wem {P = P} {Q = Q} npq with wem {P = P} | wem {P = Q}
  [weak-excluded-middle]-to-[[¬][∧]ₗ] wem {P = P} {Q = Q} npq | [∨]-introₗ np  | [∨]-introₗ nq  = [∨]-introₗ np
  [weak-excluded-middle]-to-[[¬][∧]ₗ] wem {P = P} {Q = Q} npq | [∨]-introₗ np  | [∨]-introᵣ nnq = [∨]-introₗ np
  [weak-excluded-middle]-to-[[¬][∧]ₗ] wem {P = P} {Q = Q} npq | [∨]-introᵣ nnp | [∨]-introₗ nq  = [∨]-introᵣ nq
  [weak-excluded-middle]-to-[[¬][∧]ₗ] wem {P = P} {Q = Q} npq | [∨]-introᵣ nnp | [∨]-introᵣ nnq = [⊥]-elim(Propositional.[∧]-intro nnp nnq npq)

  [[¬][∧]ₗ]-to-[weak-excluded-middle] : (∀{ℓ₁ ℓ₂}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → ((¬ P) ∨ (¬ Q)) ← (¬ (P ∧ Q))) → (∀{ℓ}{P : Stmt{ℓ}} → (¬ P) ∨ (¬¬ P))
  [[¬][∧]ₗ]-to-[weak-excluded-middle] [¬][∧]ₗ {ℓ} {P} = [¬][∧]ₗ non-contradiction
