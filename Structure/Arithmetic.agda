module Structure.Arithmetic where

import      Lvl
open import Logic
open import Logic.Predicate
open import Logic.Propositional
open import Relator.Ordering
open import Sets.Setoid
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Structure.Function.Domain
open import Syntax.Function
open import Type

private variable ℓₒ ℓₗ ℓₗ₁ ℓₗ₂ : Lvl.Level
private variable T T₁ T₂ : Type{ℓₒ}

module _ ⦃ equiv : Equiv(T) ⦄ (𝟎 : T) (𝐒 : T → T) where
  record Elemental : Type{Lvl.of(T)} where
    field
      ⦃ 𝐒-function  ⦄   : Function(𝐒)
      ⦃ 𝐒-injectivity ⦄ : Injective(𝐒)
      𝐒-positivity      : ∀{x} → (𝐒(x) ≢ 𝟎)

  module _ (_<_ : T → T → Stmt{ℓₗ}) where
    record Minimal : Type{Lvl.of(T) ⊔ ℓₗ} where
      open From-[<][≡] (_<_) (_≡_)

      field
        ⦃ elemental ⦄ : Elemental
        [<]ₗ-𝟎 : ∀{x} → (𝟎 < x) ↔ (x ≢ 𝟎)
        [<]ᵣ-𝟎 : ∀{x} → (𝟎 ≤ x) -- Minimum in the order (TODO: Is (∀x. x≥0) neccessary? Which means (0<x)∨(0=x))
        [<]ₗ-𝐒 : ∀{x y} → (𝐒(x) < y) ↔ ((x < y)∧(𝐒(x) ≢ y)) -- TODO: Also the definition of (_≤_)?
        [<]ᵣ-𝐒 : ∀{x y} → (x < 𝐒(y)) ↔ (x ≤ y)

    record Full : Typeω where
      field
        ⦃ minimal ⦄ : Minimal
        induction : ∀{ℓ}{P : T → Stmt{ℓ}} → P(𝟎) → (∀{x} → P(x) → P(𝐒(x))) → (∀{x} → P(x))

      𝟎-or-𝐒 : ∀{x} → (x ≡ 𝟎) ∨ ∃(y ↦ x ≡ 𝐒(y))
      𝟎-or-𝐒 {x} = induction {P = x ↦ (x ≡ 𝟎) ∨ ∃(y ↦ x ≡ 𝐒(y))} ([∨]-introₗ (reflexivity(_≡_))) (\{x} → [∨]-elim (p ↦ [∨]-introᵣ([∃]-intro 𝟎 ⦃ [≡]-with(𝐒) p ⦄)) (\{([∃]-intro y ⦃ p ⦄) → [∨]-introᵣ([∃]-intro (𝐒(y)) ⦃ [≡]-with(𝐒) p ⦄)})) {x}

{-
module _ ⦃ equiv : Equiv(T) ⦄ {𝟎}{𝐒}{_<_ : T → T → Stmt{ℓₗ}} ⦃ full : Full(𝟎)(𝐒)(_<_) ⦄ where
  open import Numeral.Natural as ℕ using (ℕ)
  open import Type.Empty

  -- TODO: This is a definition of an isomorphism between any of these and ℕ?

  from-ℕ : ℕ → T
  from-ℕ (ℕ.𝟎)    = 𝟎
  from-ℕ (ℕ.𝐒(n)) = 𝐒(from-ℕ n)

  to-ℕ : T → ℕ
  to-ℕ x = ◊.existence (Full.induction(full) zero succ {x}) where
    zero = intro ⦃ ℕ.𝟎 ⦄
    succ = \{(intro ⦃ n ⦄) → intro ⦃ ℕ.𝐒(n) ⦄}

  -}

{-
module _
  ⦃ equiv : Equiv(T₁) ⦄ {𝟎₁}{𝐒₁}{_<₁_ : T₁ → T₁ → Stmt{ℓₗ₁}} ⦃ full₁ : Full(𝟎₁)(𝐒₁)(_<₁_) ⦄
  ⦃ equiv : Equiv(T₂) ⦄ {𝟎₂}{𝐒₂}{_<₂_ : T₂ → T₂ → Stmt{ℓₗ₂}} ⦃ full₂ : Full(𝟎₂)(𝐒₂)(_<₂_) ⦄
  where
  open import Type.Empty

  {- TODO: Probably impossible to prove anything about this morph because nothing is stated about the "values" of Full.induction
  morph : T₁ → T₂
  morph x = ◊.existence (Full.induction(full₁) zero succ {x}) where
    zero = intro ⦃ 𝟎₂ ⦄
    succ = \{(intro ⦃ n ⦄) → intro ⦃ 𝐒₂(n) ⦄}

  morph-zero : morph(𝟎₁) ≡ 𝟎₂
  morph-zero = {!!}
  -}

  {- TODO: Termination checking fails because recursion depends on Full.𝟎-or-𝐒 which it does not know whether it "shrinks" the result or not
  morph : T₁ → T₂
  morph x with Full.𝟎-or-𝐒 (full₁) {x}
  ... | [∨]-introₗ _ = 𝟎₂
  ... | [∨]-introᵣ ([∃]-intro y) = 𝐒₂(morph y)
  -}
-}
