module List where

open import Data
open import Numeral.Natural

infixl 1000 _⤚_ _++_
infixr 1000 _⤙_

data List {lvl} (T : Set lvl) : Set lvl where
  ∅ : (List T)
  _⤙_ : T → (List T) → (List T)

_⤚_ : ∀{lvl}{T : Set lvl} → (List T) → T → (List T)
_⤚_ ∅ b = b ⤙ ∅
_⤚_ (elem ⤙ rest) b = elem ⤙ (rest ⤚ elem)

_++_ : ∀{lvl}{T : Set lvl} → (List T) → (List T) → (List T)
_++_ ∅ b = b
_++_ (elem ⤙ rest) b = elem ⤙ (rest ++ b)

pattern empty = ∅
pattern prepend elem list = elem ⤙ list
postpend = _⤚_
concat   = _++_

singleton : ∀{lvl}{T : Set lvl} → T → (List T)
singleton elem = elem ⤙ ∅

map : ∀{lvl}{T₁ T₂ : Set lvl} → (T₁ → T₂) → (List T₁) → (List T₂)
map _ ∅ = ∅
map f (elem ⤙ l) = (f elem) ⤙ (map f l)

foldₗ : ∀{lvl}{T Result : Set lvl} → (Result → T → Result) → Result → (List T) → Result
foldₗ _   result ∅ = result
foldₗ _▫_ result (elem ⤙ l) = foldₗ _▫_ (result ▫ elem) l

foldᵣ : ∀{lvl}{T Result : Set lvl} → (T → Result → Result) → Result → (List T) → Result
foldᵣ _   init ∅ = init
foldᵣ _▫_ init (elem ⤙ l) = elem ▫ (foldᵣ _▫_ init l)

index : ∀{lvl}{T : Set lvl} → ℕ → (List T) → (Option T)
index _      ∅       = Option.None
index 𝟎      (x ⤙ _) = Option.Some(x)
index (𝐒(n)) (_ ⤙ l) = index n l

first : ∀{lvl}{T : Set lvl} → ℕ → (List T) → (List T)
first _      ∅       = ∅
first 𝟎      (x ⤙ _) = x ⤙ ∅
first (𝐒(n)) (x ⤙ l) = x ⤙ (first n l)

length : ∀{lvl}{T : Set lvl} → (List T) → ℕ
length ∅ = 𝟎
length (_ ⤙ l) = 𝐒(length l)
-- foldᵣ (λ _ count → 𝐒(count)) 0 l

mapWindow2ₗ : ∀{lvl}{T : Set lvl} → (T → T → T) → (List T) → (List T)
mapWindow2ₗ f (x₁ ⤙ x₂ ⤙ l) = (f x₁ x₂) ⤙ (mapWindow2ₗ f (x₂ ⤙ l))
mapWindow2ₗ _ _ = ∅

firstElem : ∀{lvl}{T : Set lvl} → (List T) → (Option T)
firstElem ∅ = Option.None
firstElem (x ⤙ _) = Option.Some(x)

lastElem : ∀{lvl}{T : Set lvl} → (List T) → (Option T)
lastElem l = foldᵣ (λ elem _ → Option.Some(elem)) Option.None l -- TODO: Is this wrong?

_or_ : ∀{lvl}{T : Set lvl} → (List T) → (List T) → (List T)
_or_ ∅ default = default
_or_ l _ = l

List-induction : ∀{lvl}{T : Set lvl}{P : List(T) → Set} → P(∅) → (∀(x : T)(l : List(T)) → P(l) → P(x ⤙ l)) → (∀{l : List(T)} → P(l))
List-induction base next {∅} = base
List-induction base next {x ⤙ l} = next(x)(l)(List-induction base next {l})
