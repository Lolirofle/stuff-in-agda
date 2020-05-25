module Logic.Classical.DoubleNegated where

open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic
import      Lvl
open import Syntax.Type
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

  double-contrapositiveᵣ : (X → Y) → ((¬¬ X) → (¬¬ Y)) -- DoubleNegated(X → Y) → DoubleNegated(¬¬ X → ¬¬ Y)
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
  DoubleNegated = Constructive.¬¬_

  module Opers where
    infixl 1010 ¬_
    infixl 1005 _∧_
    infixl 1004 _∨_
    infixl 1000 _⟵_ _⟷_ _⟶_

    _∧_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
    _∧_ X Y = DoubleNegated(Constructive._∧_ X Y)

    _⟶_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
    _⟶_ A B = DoubleNegated(A → B)

    _⟵_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
    _⟵_ A B = DoubleNegated(A ← B)

    _⟷_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
    _⟷_ A B = DoubleNegated(Constructive._↔_ A B)

    _∨_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
    _∨_ A B = DoubleNegated(Constructive._∨_ A B)

    ⊥ : Stmt
    ⊥ = DoubleNegated(Constructive.⊥)

    ⊤ : Stmt
    ⊤ = DoubleNegated(Constructive.⊤)

    ¬_ : Stmt{ℓ} → Stmt
    ¬_ A = DoubleNegated(Constructive.¬_ A)

    ∀ₗ : (X → Stmt{ℓ}) → Stmt
    ∀ₗ P = DoubleNegated(Constructive1.∀ₗ P)

    ∃ : (X → Stmt{ℓ}) → Stmt
    ∃ P = DoubleNegated(Constructive1.∃ P)

  module _ where
    open Constructive
      using(_∧_ ; _∨_ ; _↔_ ; ⊥ ; ⊤ ; ¬_ ; ¬¬_ )
    open Constructive1 -- TODO: Should be somewhere else. This is the "Propositional" module
      using(∀ₗ ; ∃)

    -- Also called: Double-negation shifts
    [¬¬][→]-preserving : DoubleNegated(X → Y) ↔ (DoubleNegated(X) → DoubleNegated(Y))
    [¬¬][→]-preserving{X = X}{Y = Y} = Constructive.[↔]-intro l r where
      open Constructive
      open ConstructiveTheorems

      l : DoubleNegated(X → Y) ← (DoubleNegated(X) → DoubleNegated(Y))
      l = [→]ᵣ-[¬¬]-move-out ∘ [→]ₗ-[¬¬]-elim

      r : DoubleNegated(X → Y) → (DoubleNegated(X) → DoubleNegated(Y))
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

    prop-intro : X → DoubleNegated(X)
    prop-intro = ConstructiveTheorems.[¬¬]-intro

    [→]₁-intro : (X → Y) → (DoubleNegated(X) → DoubleNegated(Y))
    [→]₁-intro = double-contrapositiveᵣ

    [→]₂-intro : (X → Y → Z) → (DoubleNegated(X) → DoubleNegated(Y) → DoubleNegated(Z))
    [→]₂-intro(xyz) = (Constructive.[↔]-to-[→] [¬¬][→]-preserving) ∘ ([→]₁-intro(xyz))

    [→]₃-intro : (X → Y → Z → W) → (DoubleNegated(X) → DoubleNegated(Y) → DoubleNegated(Z) → DoubleNegated(W))
    [→]₃-intro(xyzw) = (Constructive.[↔]-to-[→] [¬¬][→]-preserving) ∘₂ ([→]₂-intro(xyzw))

    ------------------------------------------
    -- Theorems

    [→][∧]-assumptionₗ : DoubleNegated((X ∧ Y) → Z) ← DoubleNegated(X → Y → Z)
    [→][∧]-assumptionₗ = [→]₁-intro(Tuple.uncurry)

    [→][∧]-assumptionᵣ : DoubleNegated((X ∧ Y) → Z) → DoubleNegated(X → Y → Z)
    [→][∧]-assumptionᵣ = [→]₁-intro(Tuple.curry)

    [¬¬]-intro : DoubleNegated(X) → DoubleNegated(¬¬ X)
    [¬¬]-intro = ConstructiveTheorems.[¬¬]-intro

    ------------------------------------------
    -- Conjunction (AND)

    [∧]-intro : DoubleNegated(X) → DoubleNegated(Y) → DoubleNegated(X ∧ Y)
    [∧]-intro = [→]₂-intro(Constructive.[∧]-intro)

    [∧]-elimₗ : DoubleNegated(X ∧ Y) → DoubleNegated(X)
    [∧]-elimₗ = [→]₁-intro(Constructive.[∧]-elimₗ)

    [∧]-elimᵣ : DoubleNegated(X ∧ Y) → DoubleNegated(Y)
    [∧]-elimᵣ = [→]₁-intro(Constructive.[∧]-elimᵣ)

    ------------------------------------------
    -- Implication

    [→]-elim : DoubleNegated(X → Y) → DoubleNegated(X) → DoubleNegated(Y)
    [→]-elim = [→]₂-intro(swap Constructive.[→]-elim)

    [→]-intro : (DoubleNegated(X) → DoubleNegated(Y)) → DoubleNegated(X → Y)
    [→]-intro = [¬¬]-double-contrapositiveₗ

    ------------------------------------------
    -- Reverse implication

    [←]-intro : (DoubleNegated(Y) ← DoubleNegated(X)) → DoubleNegated(Y ← X)
    [←]-intro = [¬¬]-double-contrapositiveₗ

    [←]-elim : DoubleNegated(X) → DoubleNegated(Y ← X) → DoubleNegated(Y)
    [←]-elim = [→]₂-intro(Constructive.[←]-elim)

    ------------------------------------------
    -- Equivalence

    [↔]-intro : (DoubleNegated(X) ← DoubleNegated(Y)) → (DoubleNegated(X) → DoubleNegated(Y)) → DoubleNegated(X ↔ Y)
    [↔]-intro yx xy = ([→]₂-intro(Constructive.[↔]-intro)) ([→]-intro yx) ([→]-intro xy)

    [↔]-elimₗ : DoubleNegated(X ↔ Y) → DoubleNegated(X) ← DoubleNegated(Y)
    [↔]-elimₗ = [→]-elim ∘ ([→]₁-intro(Constructive.[↔]-to-[←]))

    [↔]-elimᵣ : DoubleNegated(X ↔ Y) → DoubleNegated(X) → DoubleNegated(Y)
    [↔]-elimᵣ = [→]-elim ∘ ([→]₁-intro(Constructive.[↔]-to-[→]))

    ------------------------------------------
    -- Disjunction (OR)

    [∨]-introₗ : DoubleNegated(X) → DoubleNegated(X ∨ Y)
    [∨]-introₗ = [→]₁-intro(Constructive.[∨]-introₗ)

    [∨]-introᵣ : DoubleNegated(Y) → DoubleNegated(X ∨ Y)
    [∨]-introᵣ = [→]₁-intro(Constructive.[∨]-introᵣ)

    [∨]-elim : (DoubleNegated(X) → DoubleNegated(Z)) → (DoubleNegated(Y) → DoubleNegated(Z)) → DoubleNegated(X ∨ Y) → DoubleNegated(Z)
    [∨]-elim xz yz = ([→]₃-intro(Constructive.[∨]-elim)) ([→]-intro xz) ([→]-intro yz)

    ------------------------------------------
    -- Bottom (false, absurdity, empty, contradiction)

    [⊥]-intro : DoubleNegated(X) → DoubleNegated(¬ X) → DoubleNegated(⊥)
    [⊥]-intro = [→]₂-intro(Constructive.[⊥]-intro)

    [⊥]-elim : DoubleNegated(⊥) → DoubleNegated(X)
    [⊥]-elim = [→]₁-intro(Constructive.[⊥]-elim)

    ------------------------------------------
    -- Top (true, truth, unit, validity)

    [⊤]-intro : DoubleNegated(⊤)
    [⊤]-intro = prop-intro(Constructive.[⊤]-intro)

    ------------------------------------------
    -- Negation

    [¬]-intro : (DoubleNegated(X) → DoubleNegated(⊥)) → DoubleNegated(¬ X)
    [¬]-intro = ([→]₁-intro(Constructive.[¬]-intro)) ∘ [→]-intro

    [¬]-elim : DoubleNegated(¬ X) → DoubleNegated(X → ⊥)
    [¬]-elim = [→]₁-intro(Constructive.[¬]-elim)

    ------------------------------------------
    -- For-all quantification

    -- [∀]-intro : ∀{P : X → Stmt{ℓ}} → (∀{x} → DoubleNegated(P(x))) → DoubleNegated(∀{x} → P(x))
    -- [∀]-intro {P} f g = [→]ᵣ-[¬¬]-move-out {!\x → f{x}!} {!g!}
    -- ConstructiveTheorems.[→]ᵣ-[¬¬]-move-out (f) (g)

    -- [∀]-elim : ∀{P} → DoubleNegated(∀{x} → P(x)) → ∀{x} → DoubleNegated(P(x))
    -- TODO: [→]ₗ-[¬¬]-elim

    ------------------------------------------
    -- Existential quantification

    [∃]-intro : ∀{x} → DoubleNegated(P(x)) → DoubleNegated(∃ P)
    [∃]-intro {x = x} = [→]₁-intro(proof ↦ Constructive1.[∃]-intro (x) ⦃ proof ⦄)

    ------------------------------------------
    -- Theorems exclusive to classic logic (compared to constructive logic)

    [¬¬]-elim : DoubleNegated(¬¬ X) → DoubleNegated(X)
    [¬¬]-elim = ConstructiveTheorems.[¬¬¬]-elim

    excluded-middle : DoubleNegated(X ∨ (¬ X))
    excluded-middle{X = X} = ConstructiveTheorems.[¬¬]-excluded-middle

    [¬]-elim₂ : DoubleNegated((¬ X) → ⊥) → DoubleNegated(X)
    [¬]-elim₂ = [¬¬]-elim ∘ [¬]-intro ∘ [→]-elim

    [→]-disjunctive-formᵣ : DoubleNegated(X → Y) → DoubleNegated((¬ X) ∨ Y)
    [→]-disjunctive-formᵣ n-n-x→y n-nx∨y = (n-nx∨y ∘ Constructive.[∨]-introₗ) (n-n-x→y ∘ (n-nx∨y ∘ Constructive.[∨]-introᵣ ∘₂ apply))

    contrapositiveₗ : DoubleNegated(X → Y) ← DoubleNegated((¬ X) ← (¬ Y))
    contrapositiveₗ n-n-ny→nx = [→]-intro ([¬¬]-elim ∘ ConstructiveTheorems.contrapositiveᵣ([→]-elim n-n-ny→nx) ∘ [¬¬]-intro)

    double-contrapositiveₗ : DoubleNegated(X → Y) ← DoubleNegated((¬¬ X) → (¬¬ Y))
    double-contrapositiveₗ = contrapositiveₗ ∘ contrapositiveₗ

    -- postulate callcc : DoubleNegated(((X → Y) → X) → X)
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

  -- TODO: Does not have to be over all propositions P in assumption. Only wem P and wem Q are used.
  [weak-excluded-middle]-to-[[¬][∧]ₗ] : (∀{ℓ}{P : Stmt{ℓ}} → (¬ P) ∨ (¬¬ P)) → (∀{ℓ₁ ℓ₂}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → ((¬ P) ∨ (¬ Q)) ← (¬ (P ∧ Q)))
  [weak-excluded-middle]-to-[[¬][∧]ₗ] wem {P = P} {Q = Q} npq with wem {P = P} | wem {P = Q}
  [weak-excluded-middle]-to-[[¬][∧]ₗ] wem {P = P} {Q = Q} npq | [∨]-introₗ np  | [∨]-introₗ nq  = [∨]-introₗ np
  [weak-excluded-middle]-to-[[¬][∧]ₗ] wem {P = P} {Q = Q} npq | [∨]-introₗ np  | [∨]-introᵣ nnq = [∨]-introₗ np
  [weak-excluded-middle]-to-[[¬][∧]ₗ] wem {P = P} {Q = Q} npq | [∨]-introᵣ nnp | [∨]-introₗ nq  = [∨]-introᵣ nq
  [weak-excluded-middle]-to-[[¬][∧]ₗ] wem {P = P} {Q = Q} npq | [∨]-introᵣ nnp | [∨]-introᵣ nnq = [⊥]-elim(Propositional.[∧]-intro nnp nnq npq)

  [[¬][∧]ₗ]-to-[weak-excluded-middle] : (∀{ℓ₁ ℓ₂}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → ((¬ P) ∨ (¬ Q)) ← (¬ (P ∧ Q))) → (∀{ℓ}{P : Stmt{ℓ}} → (¬ P) ∨ (¬¬ P))
  [[¬][∧]ₗ]-to-[weak-excluded-middle] [¬][∧]ₗ {ℓ} {P} = [¬][∧]ₗ non-contradiction
