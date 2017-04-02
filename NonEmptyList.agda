module NonEmptyList where

open import Data
open import Functional
open import Numeral.Natural
import List as NormalList

infixr 1000 _⊰_ _⤛_

data List {lvl} (n : ℕ) (T : Set lvl) : Set lvl where
  End : T Tuple.^ n → (List n T)
  _⊰_ : T → (List n T) → (List n T)

pattern prepend elem list = elem ⊰ list
pattern _⤛_ elem end = elem ⊰ (End end)

toList : ∀{lvl}{T : Set lvl} → (List 1 T) → (NormalList.List T)
toList (End x) = x NormalList.⊰ NormalList.∅
toList (x ⊰ l) = x NormalList.⊰ (toList l)

fromList : ∀{lvl}{T : Set lvl} → (NormalList.List T) → T → (List 1 T)
fromList NormalList.∅ default = End default
fromList (x NormalList.⊰ NormalList.∅) _ = End x
fromList (x NormalList.⊰ l) default = x ⊰ (fromList l default)

map : ∀{lvl}{T₁ T₂ : Set lvl} → (T₁ → T₂) → (List 1 T₁) → (List 1 T₂)
map f (End x) = End(f x)
map f (elem ⊰ l) = (f elem) ⊰ (map f l)

reduceₗ : ∀{lvl}{T : Set lvl} → (T → T → T) → (List 1 T) → T
reduceₗ _   (End x) = x
reduceₗ _▫_ (elem ⊰ l) = NormalList.foldₗ _▫_ elem (toList l)

reduceᵣ : ∀{lvl}{T : Set lvl} → (T → T → T) → (List 1 T) → T
reduceᵣ _   (End x) = x
reduceᵣ _▫_ (elem ⊰ l) = elem ▫ (reduceᵣ _▫_ l)

index : ∀{lvl}{T : Set lvl} → ℕ → (List 1 T) → (Option T)
index 0      (End x) = Option.Some(x)
index 0      (x ⊰ _) = Option.Some(x)
index (𝐒(n)) (_ ⊰ l) = index n l
index _      _       = Option.None

mapWindow2ₗ : ∀{lvl₁ lvl₂}{T : Set lvl₁}{R : Set lvl₂} → (T → T → R) → (List 1 T) → (NormalList.List R)
mapWindow2ₗ f (x₁ ⊰ x₂ ⊰ l) = (f x₁ x₂) NormalList.⊰ (mapWindow2ₗ f (x₂ ⊰ l))
mapWindow2ₗ f (x₁ ⊰ (End x₂)) = (f x₁ x₂) NormalList.⊰ NormalList.∅
mapWindow2ₗ f (End _) = NormalList.∅

firstElem : ∀{lvl}{T : Set lvl} → (List 1 T) → T
firstElem (End x) = x
firstElem (x ⊰ _) = x

lastElem : ∀{lvl}{T : Set lvl} → (List 1 T) → T
lastElem (End x) = x
lastElem l = reduceᵣ (_ ↦ elem ↦ elem) l

length : {T : Set} → (List 1 T) → ℕ
length (End _) = 1
length (_ ⊰ tail) = 𝐒(length tail)

-- testMapWindow0Reduce : {_▫_ : ℕ → ℕ → Set}{_∧_ : Set → Set → Set} → reduceₗ (_∧_) (fromList (mapWindow2ₗ (_▫_) (End 1)) ℕ) → ℕ
-- testMapWindow0Reduce x = x

-- testMapWindow1Reduce : {_▫_ : ℕ → ℕ → Set}{_∧_ : Set → Set → Set} → reduceₗ (_∧_) (fromList (mapWindow2ₗ (_▫_) (1 ⊰ (End 2))) ℕ) → (1 ▫ 2)
-- testMapWindow1Reduce x = x

-- testMapWindow2Reduce : {_▫_ : ℕ → ℕ → Set}{_∧_ : Set → Set → Set} → reduceₗ (_∧_) (fromList (mapWindow2ₗ (_▫_) (1 ⊰ 2 ⊰ (End 3))) ℕ) → ((1 ▫ 2) ∧ (2 ▫ 3))
-- testMapWindow2Reduce x = x
