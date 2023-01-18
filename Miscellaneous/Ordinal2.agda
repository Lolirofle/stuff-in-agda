module Miscellaneous.Ordinal2 where

open import Functional
open import Logic.Predicate
import      Lvl
open import Syntax.Function
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable f g : A → B
private variable _▫_ _▫₁_ _▫₂_ _▫₃_ : A → B → C
private variable i : T

data Ordinal{ℓ} : Type{Lvl.𝐒(ℓ)} where
  𝟎   : Ordinal
  𝐒   : Ordinal{ℓ} → Ordinal
  lim : {T : Type{ℓ}} (f : T → Ordinal{ℓ}) → Ordinal

data _≤_ {ℓ₁ ℓ₂} : Ordinal{ℓ₁} → Ordinal{ℓ₂} → Type{Lvl.𝐒(ℓ₁ Lvl.⊔ ℓ₂)}
_<_ : Ordinal{ℓ₁} → Ordinal{ℓ₂} → Type

x < y = 𝐒(x) ≤ y

data _≤_ where
  minimal  : ∀{x} → (𝟎 ≤ x)
  step     : ∀{x y} → (x ≤ y) → (𝐒(x) ≤ 𝐒(y))
  maximal  : ∀{f}{x}{i : T} → (x ≤ f(i)) → (x < lim f)
  supremum : ∀{f}{x} → (∀{i : T} → (f(i) < x)) → (lim f ≤ x)

open import Logic.Propositional

private variable x y : Ordinal{ℓ}

_≥_ : Ordinal{ℓ₁} → Ordinal{ℓ₂} → Type
_≥_ = swap(_≤_)

_>_ : Ordinal{ℓ₁} → Ordinal{ℓ₂} → Type
_>_ = swap(_<_)

_≡_ : Ordinal{ℓ₁} → Ordinal{ℓ₂} → Type
x ≡ y = (x ≥ y) ∧ (x ≤ y)

[≤]-unstep : (𝐒(x) ≤ 𝐒(y)) → (x ≤ y)
[≤]-unstep (step xy) = xy

[<]-minimal : 𝟎 {ℓ} < 𝐒(x)
[<]-minimal = step minimal

[≡]-ext-reflexivity-of-lim : (∀{x} → f(x) ≡ g(x)) → (lim f ≡ lim g)
[≡]-ext-reflexivity-of-lim ext = [∧]-intro
  (supremum(maximal([∧]-elimₗ ext)))
  (supremum(maximal([∧]-elimᵣ ext)))

[≤]-reflexivity-raw : (x ≤ x)
[≤]-reflexivity-raw {x = 𝟎} = minimal
[≤]-reflexivity-raw {x = 𝐒 x} = step [≤]-reflexivity-raw
[≤]-reflexivity-raw {x = lim f} = supremum (maximal [≤]-reflexivity-raw)

[≡]-reflexivity-raw : (x ≡ x)
[≡]-reflexivity-raw = [∧]-intro [≤]-reflexivity-raw [≤]-reflexivity-raw

lim-as-𝐒 : ∀{c : C} → lim(\(_ : C) → x) ≡ 𝐒(x)
lim-as-𝐒 {c = c} = [∧]-intro (maximal{i = c} [≤]-reflexivity-raw) (supremum (step [≤]-reflexivity-raw))

{-
open import Data
open import Data.Boolean

_≤?_ : Ordinal{ℓ₁} → Ordinal{ℓ₂} → Bool
𝟎     ≤? _     = 𝑇
𝐒 x   ≤? 𝟎     = 𝐹
𝐒 x   ≤? 𝐒 y   = x ≤? y
𝐒 x   ≤? lim g = lim{T = Unit}(const x) ≤? lim g
lim f ≤? 𝟎     = 𝐹
lim f ≤? 𝐒 y   = lim f ≤? lim{T = Unit}(const y)
lim f ≤? lim g = {!!} -- TODO: This should not be decidable in general. It is when it is possible to find a maximum element in the image of f and g (for example by checking every element when the domain of f and g are finite. There may be a maximum for infinites too, but how would they be found?)
-}
