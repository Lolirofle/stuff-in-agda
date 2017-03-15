module List where

open import Data
open import Numeral.Natural

infixl 1000 _⤚_ _⁀_
infixr 1000 _⤙_

data List {n} (T : Set n) : Set n where
  ∅ : (List T)
  _⤙_ : T → (List T) → (List T)

_⤚_ : ∀ {n} → {T : Set n} → (List T) → T → (List T)
_⤚_ ∅ b = b ⤙ ∅
_⤚_ (elem ⤙ rest) b = elem ⤙ (rest ⤚ elem)

_⁀_ : ∀ {n} → {T : Set n} → (List T) → (List T) → (List T)
_⁀_ ∅ b = b
_⁀_ (elem ⤙ rest) b = elem ⤙ (rest ⁀ b)

pattern empty = ∅
pattern prepend elem list = elem ⤙ list
postpend = _⤚_
concat   = _⁀_

singleton : ∀ {n} → {T : Set n} → T → (List T)
singleton elem = elem ⤙ ∅

map : ∀ {n} → {T₁ T₂ : Set n} → (T₁ → T₂) → (List T₁) → (List T₂)
map _ ∅ = ∅
map f (elem ⤙ l) = (f elem) ⤙ (map f l)

reduceₗ : ∀ {n} → {T Result : Set n} → (T → Result → Result) → Result → (List T) → Result
reduceₗ _   init ∅ = init
reduceₗ _▫_ init (elem ⤙ l) = elem ▫ (reduceₗ _▫_ init l)

reduceᵣ : ∀ {n} → {T Result : Set n} → (Result → T → Result) → Result → (List T) → Result
reduceᵣ _   result ∅ = result
reduceᵣ _▫_ result (elem ⤙ l) = reduceᵣ _▫_ (result ▫ elem) l

index : ∀ {n} → {T : Set n} → ℕ → (List T) → (Option T)
index _      ∅       = Option.None
index 𝟎      (x ⤙ _) = Option.Some(x)
index (𝐒(n)) (_ ⤙ l) = index n l

first : ∀ {n} → {T : Set n} → ℕ → (List T) → (List T)
first _      ∅       = ∅
first 𝟎      (x ⤙ _) = x ⤙ ∅
first (𝐒(n)) (x ⤙ l) = x ⤙ (first n l)

length : {T : Set} → (List T) → ℕ -- TODO: Make ℕ a member of (Set n), and then generalize this function
length l = reduceₗ (λ _ count → 𝐒(count)) 0 l

mapWindow2ₗ : ∀ {n} → {T : Set n} → (T → T → T) → (List T) → (List T)
mapWindow2ₗ f (x₁ ⤙ x₂ ⤙ l) = (f x₁ x₂) ⤙ (mapWindow2ₗ f (x₂ ⤙ l))
mapWindow2ₗ _ _ = ∅

firstElem : ∀ {n} → {T : Set n} → (List T) → (Option T)
firstElem ∅ = Option.None
firstElem (x ⤙ _) = Option.Some(x)

lastElem : ∀ {n} → {T : Set n} → (List T) → (Option T)
lastElem l = reduceₗ (λ elem _ → Option.Some(elem)) Option.None l

_or_ : ∀ {n} → {T : Set n} → (List T) → (List T) → (List T)
_or_ ∅ default = default
_or_ l _ = l
