module NonEmptyList where

open import Data
open import Numeral.Natural
import List as NormalList

infixr 1000 _⤙_

data List {n} (T : Set n) : Set n where
  singleton : T → (List T)
  _⤙_ : T → (List T) → (List T)

pattern prepend elem list = elem ⤙ list

map : ∀ {n} → {T₁ T₂ : Set n} → (T₁ → T₂) → (List T₁) → (List T₂)
map f (singleton x) = singleton(f x)
map f (elem ⤙ l) = (f elem) ⤙ (map f l)

reduceₗ : ∀ {n} → {T : Set n} → (T → T → T) → (List T) → T
reduceₗ _   (singleton x) = x
reduceₗ _▫_ (elem ⤙ l) = elem ▫ (reduceₗ _▫_ l)

index : ∀ {n} → {T : Set n} → ℕ → (List T) → (Option T)
index 0      (singleton x) = Option.Some(x)
index 0      (x ⤙ _)       = Option.Some(x)
index (𝐒(n)) (_ ⤙ l)       = index n l
index _      _             = Option.None

mapWindow2ₗ : ∀ {n} → {T : Set n} → (T → T → T) → (List T) → (NormalList.List T)
mapWindow2ₗ f (x₁ ⤙ x₂ ⤙ l) = (f x₁ x₂) NormalList.⤙ (mapWindow2ₗ f (x₂ ⤙ l))
mapWindow2ₗ f (x₁ ⤙ (singleton x₂)) = (f x₁ x₂) NormalList.⤙ NormalList.∅
mapWindow2ₗ f (singleton x) = NormalList.∅

firstElem : ∀ {n} → {T : Set n} → (List T) → T
firstElem (singleton x) = x
firstElem (x ⤙ _)       = x

lastElem : ∀ {n} → {T : Set n} → (List T) → T
lastElem (singleton x) = x
lastElem l = reduceₗ (λ elem _ → elem) l

toList : ∀ {n} → {T : Set n} → (List T) → (NormalList.List T)
toList (singleton x) = x NormalList.⤙ NormalList.∅
toList (x ⤙ l) = x NormalList.⤙ (toList l)
