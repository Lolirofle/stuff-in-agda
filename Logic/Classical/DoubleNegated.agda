module Logic.Classical.DoubleNegated where

open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Names
open import Logic.Propositional as Constructive using (¬¬_)
import      Logic.Predicate     as Constructive
open import Logic
import      Lvl
open import Syntax.Type
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable X Y Z W : Stmt{ℓ}
private variable P : X → Stmt{ℓ}

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
module _ where
  infixl 1011 •_
  infixl 1010 ¬_
  infixl 1005 _∧_
  infixl 1004 _∨_
  infixl 1000 _⟵_ _⟷_ _⟶_

  •_ : Stmt{ℓ} → Stmt
  •_ = ¬¬_

  _∧_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  _∧_ = (¬¬_) ∘₂ (Constructive._∧_)

  _⟶_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  _⟶_ = (¬¬_) ∘₂ (_→ᶠ_)

  _⟵_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  _⟵_ = (¬¬_) ∘₂ (_←_)

  _⟷_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  _⟷_ = (¬¬_) ∘₂ (Constructive._↔_)

  _∨_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  _∨_ = (¬¬_) ∘₂ (Constructive._∨_)

  ⊥ : Stmt
  ⊥ = ¬¬ Constructive.⊥

  ⊤ : Stmt
  ⊤ = ¬¬ Constructive.⊤

  ¬_ : Stmt{ℓ} → Stmt
  ¬_ = (¬¬_) ∘ Constructive.¬_

  ∀ₗ : (X → Stmt{ℓ}) → Stmt
  ∀ₗ = (¬¬_) ∘ Constructive.∀ₗ ∘ ((¬¬_) ∘_)

  ∃ : (X → Stmt{ℓ}) → Stmt
  ∃ = (¬¬_) ∘ Constructive.∃

  import      Logic.Propositional.Theorems as Constructive
  import      Logic.Predicate.Theorems     as Constructive

  [→]ₗ-[¬¬]-elim : ((¬¬ X) → Y) → (X → Y)
  [→]ₗ-[¬¬]-elim = liftᵣ(Constructive.[¬¬]-intro)

  [→]ᵣ-[¬¬]-move-out : (X → (¬¬ Y)) → ¬¬(X → Y)
  [→]ᵣ-[¬¬]-move-out xnny nxy = nxy (x ↦ Constructive.[⊥]-elim(xnny x (y ↦ nxy (const y))))

  double-contrapositiveᵣ : (X → Y) → ((¬¬ X) → (¬¬ Y)) -- DoubleNegated(X → Y) → DoubleNegated(¬¬ X → ¬¬ Y)
  double-contrapositiveᵣ = Constructive.contrapositiveᵣ ∘ Constructive.contrapositiveᵣ

  [¬¬]-double-contrapositiveₗ : ¬¬(X → Y) ← ((¬¬ X) → (¬¬ Y))
  [¬¬]-double-contrapositiveₗ p = [→]ᵣ-[¬¬]-move-out ([→]ₗ-[¬¬]-elim p)

  -- Also called: Double-negation shift.
  [¬¬][→]-preserving : ¬¬(X → Y) Constructive.↔ ((¬¬ X) → (¬¬ Y))
  [¬¬][→]-preserving{X = X}{Y = Y} = Constructive.[↔]-intro l r where
    l : ¬¬(X → Y) ← ((¬¬ X) → (¬¬ Y))
    l = [→]ᵣ-[¬¬]-move-out ∘ [→]ₗ-[¬¬]-elim

    r : ¬¬(X → Y) → ((¬¬ X) → (¬¬ Y))
    r(nnxy)(nnx)(ny) =
      ((Constructive.[→]-elim
        ((xy ↦
          ((Constructive.[→]-elim
            ((Constructive.[→]-elim
              ((Constructive.[⊥]-elim
                ((Constructive.[→]-elim
                  ((x ↦
                    ((Constructive.[→]-elim
                      ((Constructive.[→]-elim x xy) :of: Y)
                      (ny :of: (Y → Constructive.⊥))
                    ) :of: Constructive.⊥)
                  ) :of: (X → Constructive.⊥))
                  (nnx :of: ((X → Constructive.⊥) → Constructive.⊥))
                ) :of: Constructive.⊥)
              ) :of: X)
              (xy :of: (X → Y))
            ) :of: Y)
            (ny :of: (Y → Constructive.⊥))
          ) :of: Constructive.⊥)
        ) :of: ((X → Y) → Constructive.⊥))
        (nnxy :of: ¬¬(X → Y))
      ) :of: Constructive.⊥)

  ------------------------------------------
  -- Converting theorems with implication in constructive logic to classical logic

  prop-intro : X → (¬¬ X)
  prop-intro = Constructive.[¬¬]-intro

  [→]₁-intro : (X → Y) → ((¬¬ X) → (¬¬ Y))
  [→]₁-intro = double-contrapositiveᵣ

  [→]₂-intro : (X → Y → Z) → ((¬¬ X) → (¬¬ Y) → (¬¬ Z))
  [→]₂-intro(xyz) = (Constructive.[↔]-to-[→] [¬¬][→]-preserving) ∘ ([→]₁-intro(xyz))

  [→]₃-intro : (X → Y → Z → W) → ((¬¬ X) → (¬¬ Y) → (¬¬ Z) → (¬¬ W))
  [→]₃-intro(xyzw) = (Constructive.[↔]-to-[→] [¬¬][→]-preserving) ∘₂ ([→]₂-intro(xyzw))

  ------------------------------------------
  -- Theorems

  [→][∧]-assumptionₗ : ¬¬((X Constructive.∧ Y) → Z) ← ¬¬(X → Y → Z)
  [→][∧]-assumptionₗ = [→]₁-intro(Tuple.uncurry)

  [→][∧]-assumptionᵣ : ¬¬((X Constructive.∧ Y) → Z) → ¬¬(X → Y → Z)
  [→][∧]-assumptionᵣ = [→]₁-intro(Tuple.curry)

  [¬¬]-intro : (¬¬ X) → ¬¬(¬¬ X)
  [¬¬]-intro = Constructive.[¬¬]-intro

  ------------------------------------------
  -- Conjunction (AND)

  [∧]-intro : (• X) → (• Y) → (X ∧ Y)
  [∧]-intro = [→]₂-intro Constructive.[∧]-intro

  [∧]-elimₗ : (X ∧ Y) → (• X)
  [∧]-elimₗ = [→]₁-intro Constructive.[∧]-elimₗ

  [∧]-elimᵣ : (X ∧ Y) → (• Y)
  [∧]-elimᵣ = [→]₁-intro Constructive.[∧]-elimᵣ

  ------------------------------------------
  -- Implication

  [→]-elim : (X ⟶ Y) → (• X) → (• Y)
  [→]-elim = [→]₂-intro(swap Constructive.[→]-elim)

  [→]-intro : ((• X) → (• Y)) → (X ⟶ Y)
  [→]-intro = [¬¬]-double-contrapositiveₗ

  ------------------------------------------
  -- Reverse implication

  [←]-intro : ((• Y) ← (• X)) → (Y ⟵ X)
  [←]-intro = [¬¬]-double-contrapositiveₗ

  [←]-elim : (• X) → (Y ⟵ X) → (• Y)
  [←]-elim = [→]₂-intro(Constructive.[←]-elim)

  ------------------------------------------
  -- Equivalence

  [↔]-intro : ((• X) ← (• Y)) → ((• X) → (• Y)) → (X ⟷ Y)
  [↔]-intro yx xy = ([→]₂-intro(Constructive.[↔]-intro)) ([→]-intro yx) ([→]-intro xy)

  [↔]-elimₗ : (X ⟷ Y) → (• X) ← (• Y)
  [↔]-elimₗ = [→]-elim ∘ ([→]₁-intro(Constructive.[↔]-to-[←]))

  [↔]-elimᵣ : (X ⟷ Y) → (• X) → (• Y)
  [↔]-elimᵣ = [→]-elim ∘ ([→]₁-intro(Constructive.[↔]-to-[→]))

  ------------------------------------------
  -- Disjunction (OR)

  [∨]-introₗ : (• X) → (X ∨ Y)
  [∨]-introₗ = [→]₁-intro(Constructive.[∨]-introₗ)

  [∨]-introᵣ : (• Y) → (X ∨ Y)
  [∨]-introᵣ = [→]₁-intro(Constructive.[∨]-introᵣ)

  [∨]-elim : ((• X) → (• Z)) → ((• Y) → (• Z)) → (X ∨ Y) → (¬¬ Z)
  [∨]-elim xz yz = ([→]₃-intro(Constructive.[∨]-elim)) ([→]-intro xz) ([→]-intro yz)

  ------------------------------------------
  -- Bottom (false, absurdity, empty, contradiction)

  [⊥]-intro : (• X) → (¬ X) → ⊥
  [⊥]-intro = [→]₂-intro(Constructive.[⊥]-intro)

  [⊥]-elim : ⊥ → (• X)
  [⊥]-elim = [→]₁-intro(Constructive.[⊥]-elim)

  ------------------------------------------
  -- Top (true, truth, unit, validity)

  [⊤]-intro : ⊤
  [⊤]-intro = prop-intro(Constructive.[⊤]-intro)

  ------------------------------------------
  -- Negation

  [¬]-intro : ((• X) → ⊥) → (¬ X)
  [¬]-intro = ([→]₁-intro(Constructive.[¬]-intro)) ∘ [→]-intro

  [¬]-elim : ((¬ X) → ⊥) → (• X)
  [¬]-elim nnx nx = nnx (apply nx) id

  ------------------------------------------
  -- For-all quantification

  [∀]-intro : (∀{x} → • P(x)) → (∀ₗ P)
  [∀]-intro = apply

  [∀]-elim : (∀ₗ P) → ∀{x} → • P(x)
  [∀]-elim apx npx = apx(\px → apply npx px)

  ------------------------------------------
  -- Existential quantification

  [∃]-intro : ∀{x} → • P(x) → (∃ P)
  [∃]-intro {x = x} = [→]₁-intro(proof ↦ Constructive.[∃]-intro (x) ⦃ proof ⦄)

  [∃]-elim : (∀{x} → • P(x) → • X) → (∃ P) → • X
  [∃]-elim apx nnep nx = nnep (Constructive.[∃]-elim (p ↦ apx (apply p) nx))

  ------------------------------------------
  -- Theorems exclusive to classic logic (compared to constructive logic)

  [¬¬]-elim : ¬¬(¬¬ X) → (• X)
  [¬¬]-elim = Constructive.[¬¬¬]-elim

  excluded-middle : (X ∨ (Constructive.¬ X))
  excluded-middle{X = X} = Constructive.[¬¬]-excluded-middle

  [→]-disjunctive-formᵣ : (X ⟶ Y) → (Constructive.¬ X ∨ Y)
  [→]-disjunctive-formᵣ n-n-x→y n-nx∨y = (n-nx∨y ∘ Constructive.[∨]-introₗ) (n-n-x→y ∘ (n-nx∨y ∘ Constructive.[∨]-introᵣ ∘₂ apply))

  -- contrapositiveₗ : (X ⟶ Y) ← ((Constructive.¬ X) ⟵ (Constructive.¬ Y))
  -- contrapositiveₗ n-n-ny→nx = {!!}
  -- Constructive.[→]-intro ([¬¬]-elim ∘ Constructive.contrapositiveᵣ(Constructive.[→]-elim n-n-ny→nx) ∘ Constructive.[¬¬]-intro)

module _ where
  _∨ʷᵉᵃᵏ_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
  X ∨ʷᵉᵃᵏ Y = Constructive.¬((Constructive.¬ X) Constructive.∧ (Constructive.¬ Y))

  [∨ʷᵉᵃᵏ]-introₗ : X → (X ∨ʷᵉᵃᵏ Y)
  [∨ʷᵉᵃᵏ]-introₗ = swap Constructive.[∧]-elimₗ

  [∨ʷᵉᵃᵏ]-introᵣ : Y → (X ∨ʷᵉᵃᵏ Y)
  [∨ʷᵉᵃᵏ]-introᵣ = swap Constructive.[∧]-elimᵣ

  [∨ʷᵉᵃᵏ]-elim : (X → Z) → (Y → Z) → DoubleNegationOn(Z) → (X ∨ʷᵉᵃᵏ Y) → Z
  [∨ʷᵉᵃᵏ]-elim xz yz nnzz xy = nnzz(nz ↦ xy(Constructive.[∧]-intro (nz ∘ xz) (nz ∘ yz)))

  ∃ʷᵉᵃᵏ : (X → Stmt{ℓ}) → Stmt
  ∃ʷᵉᵃᵏ P = Constructive.¬(∀{x} → (Constructive.¬ P(x)))

  [∃ʷᵉᵃᵏ]-intro : ∀(x) → ⦃ proof : P(x) ⦄ → (∃ʷᵉᵃᵏ P)
  [∃ʷᵉᵃᵏ]-intro _ ⦃ px ⦄ axnpx = axnpx px

  [∃ʷᵉᵃᵏ]-elim : (∀{x} → P(x) → X) → DoubleNegationOn(X) → (∃ʷᵉᵃᵏ P) → X
  [∃ʷᵉᵃᵏ]-elim axpxx nnxx ep = nnxx(ep ∘ (_∘ axpxx))
