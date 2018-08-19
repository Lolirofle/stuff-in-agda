module Logic.Classical{ℓ} where

open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Propositional.Theorems{ℓ}

-- A proposition which is either provable or unprovable.
-- This could then be interpreted as true or false.
-- Also called: Decidable
record Classical (P : Stmt) : Stmt where
  instance constructor classical-intro
  field
    ⦃ excluded-middle ⦄ : P ∨ (¬ P)

  [¬¬]-elim : (¬¬ P) → P
  [¬¬]-elim = [¬¬]-elim-from-excluded-middle (excluded-middle)

  contrapositiveₗ : ∀{Q : Stmt} → (Q → P) ← ((¬ Q) ← (¬ P))
  contrapositiveₗ (nqnp) = [¬¬]-elim ∘ (contrapositiveᵣ (nqnp)) ∘ [¬¬]-intro
    -- (¬ X) ← (¬ Y)
    -- (¬ Y) → (¬ X)
    -- (Y → ⊥) → (X → ⊥)
    -- (Y → ⊥) → X → ⊥
    -- X → (Y → ⊥) → ⊥
    -- X → ((Y → ⊥) → ⊥)
    -- X → (¬ (Y → ⊥))
    -- X → (¬ (¬ Y))

  material-implᵣ : ∀{Q : Stmt} → (P → Q) → ((¬ P) ∨ Q)
  material-implᵣ (pq) with excluded-middle
  ... | [∨]-introₗ(p)  = [∨]-introᵣ(pq(p))
  ... | [∨]-introᵣ(np) = [∨]-introₗ(np)

  [→][∧]ₗ : ∀{Q : Stmt} → (Q → P) ← ¬(Q ∧ (¬ P))
  [→][∧]ₗ (nqnp) = [¬¬]-elim ∘ (Tuple.curry(nqnp))
    -- ¬(A ∧ ¬B) → (A → ¬¬B)
    --   ¬(A ∧ (¬ B)) //assumption
    --   ((A ∧ (B → ⊥)) → ⊥) //Definition: (¬)
    --   (A → (B → ⊥) → ⊥) //Tuple.curry
    --   (A → ¬(B → ⊥)) //Definition: (¬)
    --   (A → ¬(¬ B)) //Definition: (¬)

  call-cc : ∀{Q : Stmt} → (((P → Q) → P) → P)
  call-cc (pqp) with excluded-middle
  ... | ([∨]-introₗ p ) = p
  ... | ([∨]-introᵣ np) = pqp([⊥]-elim ∘ np)

  contrapositive-variantₗ : ∀{Q : Stmt} → ((¬ P) → Q) → (P ← (¬ Q))
  contrapositive-variantₗ {Q} npq nq = nqnp(nq) where
    npnnq : (¬ P) → (¬¬ Q)
    npnnq = [¬¬]-intro ∘ npq

    nqnp : (¬ Q) → P
    nqnp = contrapositiveₗ (npnnq)

open Classical ⦃ ... ⦄ public

{- TODO: Seems impossible to get the y
instance
  [∧]-classical-elimₗ : ∀{X Y} → ⦃ _ : Classical(X ∧ Y) ⦄ → Classical(X)
  [∧]-classical-elimₗ {X}{Y} ⦃ classical-xy ⦄ = classical-intro (proof) where
    proof : X ∨ (¬ X)
    proof with excluded-middle ⦃ classical-xy ⦄
    ... | [∨]-introₗ(xy)  = [∨]-introₗ([∧]-elimₗ(xy))
    ... | [∨]-introᵣ(nxy) = [∨]-introᵣ(x ↦ nxy([∧]-intro(x)(y)))
-}

instance
  [∧]-classical-intro : ∀{X Y} → ⦃ _ : Classical(X) ⦄ → ⦃ _ : Classical(Y) ⦄ → Classical(X ∧ Y)
  [∧]-classical-intro {X}{Y} ⦃ classical-x ⦄ ⦃ classical-y ⦄ = classical-intro ⦃ proof ⦄ where
    proof : (X ∧ Y) ∨ (¬ (X ∧ Y))
    proof with (excluded-middle ⦃ classical-x ⦄ , excluded-middle ⦃ classical-y ⦄)
    ... | ([∨]-introₗ(x)  , [∨]-introₗ(y))  = [∨]-introₗ([∧]-intro(x)(y))
    ... | ([∨]-introₗ(x)  , [∨]-introᵣ(ny)) = [∨]-introᵣ(xy ↦ ny([∧]-elimᵣ(xy)))
    ... | ([∨]-introᵣ(nx) , [∨]-introₗ(y))  = [∨]-introᵣ(xy ↦ nx([∧]-elimₗ(xy)))
    ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introᵣ(xy ↦ nx([∧]-elimₗ(xy)))

instance
  [¬]-classical-intro : ∀{X} → ⦃ _ : Classical(X) ⦄ → Classical(¬ X)
  [¬]-classical-intro {X} ⦃ classical-x ⦄ = classical-intro ⦃ proof ⦄ where
    proof : (¬ X) ∨ (¬¬ X)
    proof = Either.swap(Either.mapLeft [¬¬]-intro (excluded-middle ⦃ classical-x ⦄))

instance
  [∨]-classical-intro : ∀{X Y} → ⦃ _ : Classical(X) ⦄ → ⦃ _ : Classical(Y) ⦄ → Classical(X ∨ Y)
  [∨]-classical-intro {X}{Y} ⦃ classical-x ⦄ ⦃ classical-y ⦄ = classical-intro ⦃ proof ⦄ where
    proof : (X ∨ Y) ∨ (¬ (X ∨ Y))
    proof with (excluded-middle ⦃ classical-x ⦄ , excluded-middle ⦃ classical-y ⦄)
    ... | ([∨]-introₗ(x)  , [∨]-introₗ(y))  = [∨]-introₗ([∨]-introₗ(x))
    ... | ([∨]-introₗ(x)  , [∨]-introᵣ(ny)) = [∨]-introₗ([∨]-introₗ(x))
    ... | ([∨]-introᵣ(nx) , [∨]-introₗ(y))  = [∨]-introₗ([∨]-introᵣ(y))
    ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introᵣ(xy ↦ [∨]-elim(nx)(ny) (xy))

instance
  [→]-classical-intro : ∀{X Y} → ⦃ _ : Classical(X) ⦄ → ⦃ _ : Classical(Y) ⦄ → Classical(X → Y)
  [→]-classical-intro {X}{Y} ⦃ classical-x ⦄ ⦃ classical-y ⦄ = classical-intro ⦃ proof ⦄ where
    proof : (X → Y) ∨ (¬ (X → Y))
    proof with (excluded-middle ⦃ classical-x ⦄ , excluded-middle ⦃ classical-y ⦄)
    ... | ([∨]-introₗ(x)  , [∨]-introₗ(y))  = [∨]-introₗ(const(y))
    ... | ([∨]-introₗ(x)  , [∨]-introᵣ(ny)) = [∨]-introᵣ([¬→][∧]ₗ ([∧]-intro x ny))
    ... | ([∨]-introᵣ(nx) , [∨]-introₗ(y))  = [∨]-introₗ(const(y))
    ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introₗ([⊥]-elim ∘ nx)

instance
  [↔]-classical-intro : ∀{X Y} → ⦃ _ : Classical(X) ⦄ → ⦃ _ : Classical(Y) ⦄ → Classical(X ↔ Y)
  [↔]-classical-intro {X}{Y} ⦃ classical-x ⦄ ⦃ classical-y ⦄ = classical-intro ⦃ proof ⦄ where
    proof : (X ↔ Y) ∨ (¬ (X ↔ Y))
    proof with (excluded-middle ⦃ classical-x ⦄ , excluded-middle ⦃ classical-y ⦄)
    ... | ([∨]-introₗ(x)  , [∨]-introₗ(y))  = [∨]-introₗ([↔]-intro (const(x)) (const(y)))
    ... | ([∨]-introₗ(x)  , [∨]-introᵣ(ny)) = [∨]-introᵣ(([¬→][∧]ₗ ([∧]-intro x ny)) ∘ [↔]-elimᵣ)
    ... | ([∨]-introᵣ(nx) , [∨]-introₗ(y))  = [∨]-introᵣ(([¬→][∧]ₗ ([∧]-intro y nx)) ∘ [↔]-elimₗ)
    ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introₗ([↔]-intro ([⊥]-elim ∘ ny) ([⊥]-elim ∘ nx))

instance
  [⊤]-classical : Classical(⊤)
  [⊤]-classical = classical-intro ⦃ proof ⦄ where
    proof : ⊤ ∨ (¬ ⊤)
    proof = [∨]-introₗ ([⊤]-intro)

instance
  [⊥]-classical : Classical(⊥)
  [⊥]-classical = classical-intro ⦃ proof ⦄ where
    proof : ⊥ ∨ (¬ ⊥)
    proof = [∨]-introᵣ (id)

[¬][∧]ₗ : ∀{X Y : Stmt} → ⦃ _ : Classical(X) ⦄ → ⦃ _ : Classical(Y) ⦄ → ((¬ X) ∨ (¬ Y)) ← (¬ (X ∧ Y))
[¬][∧]ₗ {X}{Y} ⦃ classic-x ⦄ ⦃ classic-y ⦄ (nxy) =
  material-implᵣ {X} ⦃ classic-x ⦄ {¬ Y} ([→][∧]ₗ ⦃ [¬]-classical-intro ⦃ classic-y ⦄ ⦄ (nxy ∘ (Tuple.mapRight ([¬¬]-elim ⦃ classic-y ⦄))))
  -- ((X ∧ Y) → ⊥) → ((X → ⊥) ∨ (Y → ⊥))
  -- ¬((X ∧ Y) → ⊥) ← ¬((X → ⊥) ∨ (Y → ⊥))

-- TODO: Is this provable constructively? Doesn't seem like it?
[¬→][∧]ᵣ : ∀{X Y : Stmt} → ⦃ _ : Classical(X) ⦄ → ⦃ _ : Classical(Y) ⦄ → ¬(X → Y) → (X ∧ (¬ Y))
[¬→][∧]ᵣ ⦃ classic-x ⦄ ⦃ classic-y ⦄ = contrapositive-variantₗ ⦃ [∧]-classical-intro ⦃ classic-x ⦄ ⦃ [¬]-classical-intro ⦃ classic-y ⦄ ⦄ ⦄ ([→][∧]ₗ ⦃ classic-y ⦄)
