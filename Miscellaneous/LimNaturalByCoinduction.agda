{-# OPTIONS --guardedness #-}

module Miscellaneous.LimNaturalByCoinduction where

open import Data
open import Data.Option using (Option ; None ; Some)
import      Lvl
open import Type

record ℕ∞ : Type{Lvl.𝟎} where
  constructor natInf
  coinductive
  field 𝐏 : Option(ℕ∞)
open ℕ∞ public

𝟎 : ℕ∞
𝐏(𝟎) = None
-- pattern 𝟎 = natInf None

𝐒 : ℕ∞ → ℕ∞
𝐏(𝐒(n)) = Some(n)
-- pattern 𝐒(n) = natInf(Some(n)) -- TODO: Agda crashes when using this pattern synonym (Agda version 2.6.2-caeadac)

𝟏 : ℕ∞
𝟏 = 𝐒(𝟎)

∞ : ℕ∞
𝐏(∞) = Some(∞)



module _ where
  open import Logic.Propositional

  {-
  module _ {ℓ ℓₗ}{T : Type{ℓ}} (_≡_ : T → T → Type{ℓₗ}) where
    {-
    data _≡ₒₚₜ_ : Option(T) → Option(T) → Type{ℓ Lvl.⊔ ℓₗ} where
      none : (None ≡ₒₚₜ None)
      some : ∀{x y} → (x ≡ y) → (Some x ≡ₒₚₜ Some y)

    module _ (refl : ∀{x} → (x ≡ x)) where
      [≡ₒₚₜ]-reflexivity-raw : ∀{x} → (x ≡ₒₚₜ x)
      [≡ₒₚₜ]-reflexivity-raw {None}   = none
      [≡ₒₚₜ]-reflexivity-raw {Some x} = some(refl{x})
    -}

    {-
    _≡ₒₚₜ_ : Option(T) → Option(T) → Type{ℓₗ}
    None   ≡ₒₚₜ None   = Unit
    None   ≡ₒₚₜ Some x = Empty
    Some x ≡ₒₚₜ None   = Empty
    Some x ≡ₒₚₜ Some y = x ≡ y

    module _ (refl : ∀{x} → (x ≡ x)) where
      [≡ₒₚₜ]-reflexivity-raw : ∀{x} → (x ≡ₒₚₜ x)
      [≡ₒₚₜ]-reflexivity-raw {None}   = <>
      [≡ₒₚₜ]-reflexivity-raw {Some x} = refl{x}
    -}
  -}

  -- Equivalence of ℕ∞.
  -- Uses coinduction to delay the computation so that this definition terminates properly (This cannot be made into a function definition).
  -- Uses induction-coinduction to satisfy the termination checker for definitions using this equivalence.
  record _≡_ (l : ℕ∞) (r : ℕ∞) : Type{Lvl.𝟎}
  data _≡ₒₚₜ_ : Option(ℕ∞) → Option(ℕ∞) → Type{Lvl.𝟎}

  record _≡_ l r where
    coinductive
    field proof : _≡ₒₚₜ_ (𝐏(l)) (𝐏(r))
  _≢_ : ℕ∞ → ℕ∞ → Type
  l ≢ r = ¬(l ≡ r)

  data _≡ₒₚₜ_ where
    none : (None ≡ₒₚₜ None)
    some : ∀{x y} → (x ≡ y) → (Some x ≡ₒₚₜ Some y)
  unsome : ∀{x y} → (x ≡ y) ← (Some x ≡ₒₚₜ Some y)
  unsome (some p) = p

  [≡]-reflexivity-raw : ∀{x} → (x ≡ x)
  [≡ₒₚₜ]-reflexivity-raw : ∀{x} → (x ≡ₒₚₜ x)
  _≡_.proof ([≡]-reflexivity-raw {x}) = [≡ₒₚₜ]-reflexivity-raw {𝐏(x)}
  [≡ₒₚₜ]-reflexivity-raw {None}   = none
  [≡ₒₚₜ]-reflexivity-raw {Some x} = some([≡]-reflexivity-raw{x})



module _ where
  -- Alternative definition: 𝐏(x + y) = Option.partialMap (𝐏(x)) (\py → Some(x + py)) (𝐏(y))
  _+_ : ℕ∞ → ℕ∞ → ℕ∞
  𝐏(x + y) with 𝐏(y)
  ... | None    = 𝐏(x)
  ... | Some py = Some(x + py)



module Test where
  ∞' : ℕ∞
  𝐏(∞') = Some(∞')

  test1 : ∞ ≡ ∞'
  _≡_.proof test1 = some test1

  test2 : ∞ ≢ 𝟎
  test2 p with () ← _≡_.proof p

  test3 : 𝟏 ≢ 𝟎
  test3 p with () ← _≡_.proof p

  test4 : ∞ ≢ 𝟏
  test4 p with () ← _≡_.proof(unsome(_≡_.proof p))

  test5 : ∞ ≡ 𝐒(∞)
  _≡_.proof test5 = [≡ₒₚₜ]-reflexivity-raw {Some ∞}
