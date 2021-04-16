module Data.ListSized.Functions where

import      Lvl
open import Data.ListSized
open import Functional
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Function
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A A₁ A₂ B B₁ B₂ Result : Type{ℓ}
private variable a b n n₁ n₂ : ℕ

-- List concatenation
_++_ : List(T)(a) → List(T)(b) → List(T)(a + b)
_++_ x y = elim _ (\{a} → const(List _ (a + _))) y (const ∘ (_⊰_)) x
infixl 1000 _++_

-- The first element of the list
head : List(T)(𝐒(n)) → T
head (x ⊰ _) = x

-- The list without its first element
tail : List(T)(𝐒(n)) → List(T)(n)
tail (_ ⊰ l) = l

tail₀ : List(T)(n) → List(T)(𝐏(n))
tail₀ ∅       = ∅
tail₀ (_ ⊰ l) = l

-- The nth element in the list
index : 𝕟(n) → List(T)(n) → T
index 𝟎      (x ⊰ _) = x
index (𝐒(n)) (_ ⊰ l) = index n l

-- The sublist with the first n elements in the list
first : (k : 𝕟₌(n)) → List(T)(n) → List(T)(𝕟-to-ℕ k)
first 𝟎      _       = ∅
first (𝐒(n)) (x ⊰ l) = x ⊰ (first n l)

-- skip : ∀{n} → (k : 𝕟₌(n)) → List(T)(n) → List(T)(n − k)
-- last : ∀{n} → (k : 𝕟₌(n)) → List(T)(n) → List(T)(𝕟-to-ℕ k)

-- Length of the list (number of elements in the list)
length : List(T)(n) → ℕ
length {n = n} _ = n

-- The list with an element repeated n times
repeat : T → (n : ℕ) → List(T)(n)
repeat _ 𝟎      = ∅
repeat x (𝐒(n)) = x ⊰ (repeat x n)

-- A list constructed from a function
fromFn : (𝕟(n) → T) → List(T)(n)
fromFn {n = 𝟎}    _ = ∅
fromFn {n = 𝐒(n)} f = f(𝟎) ⊰ fromFn {n = n} (f ∘ 𝐒)

-- The list with a list concatenated (repeated) n times
_++^_ : List(T)(n) → (k : ℕ) → List(T)(n ⋅ k)
_++^_ _ 𝟎      = ∅
_++^_ l (𝐒(k)) = l ++ (l ++^ k)

-- Applies a function to each element in the list
map : (A → B) → List(A)(n) → List(B)(n)
map f = elim _ (\{n} _ → List(_)(n)) ∅ (const ∘ (_⊰_) ∘ f)

-- Applies a binary operator to each element in the list starting with the initial element.
-- Example:
--   foldₗ(▫)(init)[]          = init
--   foldₗ(▫)(init)[a]         = init▫a
--   foldₗ(▫)(init)[a,b]       = (init▫a)▫b
--   foldₗ(▫)(init)[a,b,c,d,e] = ((((init▫a)▫b)▫c)▫d)▫e
foldₗ : (Result → T → Result) → Result → List(T)(n) → Result
foldₗ _    result ∅ = result
foldₗ(_▫_) result (elem ⊰ l) = foldₗ(_▫_) (result ▫ elem) l

-- Applies a binary operator to each element in the list starting with the initial element.
-- Example:
--   foldᵣ(▫)(init)[]          = init
--   foldᵣ(▫)(init)[a]         = a▫init
--   foldᵣ(▫)(init)[a,b]       = a▫(b▫init)
--   foldᵣ(▫)(init)[a,b,c,d,e] = a▫(b▫(c▫(d▫(e▫init))))
foldᵣ : (T → Result → Result) → Result → List(T)(n) → Result
foldᵣ(_▫_) init = elim _ _ init (const ∘ (_▫_))

-- Example:
--   reduceₗ(▫)[a]         = a
--   reduceₗ(▫)[a,b]       = a▫b
--   reduceₗ(▫)[a,b,c]     = (a▫b)▫c
--   reduceₗ(▫)[a,b,c,d,e] = (((a▫b)▫c)▫d)▫e
reduceₗ : (T → T → T) → List(T)(𝐒(n)) → T
reduceₗ(_▫_) (elem ⊰ l) = foldₗ(_▫_) elem l

-- Example:
--   reduceᵣ(▫)[a]         = a
--   reduceᵣ(▫)[a,b]       = a▫b
--   reduceᵣ(▫)[a,b,c]     = a▫(b▫c)
--   reduceᵣ(▫)[a,b,c,d,e] = a▫(b▫(c▫(d▫e)))
reduceᵣ : (T → T → T) → List(T)(𝐒(n)) → T
reduceᵣ(_▫_) (elem ⊰ l) = foldᵣ(_▫_) elem l

map₂ : (A₁ → A₂ → B) → (List(A₁)(n₁) → List(B)(n₁)) → (List(A₂)(n₂) → List(B)(n₂)) → (List(A₁)(n₁) → List(A₂)(n₂) → List(B)(max n₁ n₂))
map₂ f g₁ g₂ ∅          ∅          = ∅
map₂ f g₁ g₂ ∅          l₂@(_ ⊰ _) = g₂ l₂
map₂ f g₁ g₂ l₁@(_ ⊰ _) ∅          = g₁ l₁
map₂ f g₁ g₂ (x₁ ⊰ l₁)  (x₂ ⊰ l₂)  = f x₁ x₂ ⊰ map₂ f (tail ∘ g₁ ∘ (x₁ ⊰_)) ((tail ∘ g₂ ∘ (x₂ ⊰_))) l₁ l₂

map₂₌ : (A₁ → A₂ → B) → (List(A₁)(n) → List(A₂)(n) → List(B)(n))
map₂₌ f ∅          ∅          = ∅
map₂₌ f (x₁ ⊰ l₁)  (x₂ ⊰ l₂)  = f x₁ x₂ ⊰ map₂₌ f l₁ l₂

-- Accumulates the results of every step in `_^_` into a list.
-- Example:
--   accumulateIterate₀ 0 f(x) = []
--   accumulateIterate₀ 1 f(x) = [x]
--   accumulateIterate₀ 2 f(x) = [x , f(x)]
--   accumulateIterate₀ 3 f(x) = [x , f(x) , f(f(x))]
--   accumulateIterate₀ 4 f(x) = [x , f(x) , f(f(x)) , f(f(f(x)))]
accumulateIterate₀ : (n : ℕ) → (T → T) → (T → List(T)(n))
accumulateIterate₀ 𝟎      f(x) = ∅
accumulateIterate₀ (𝐒(n)) f(x) = x ⊰ accumulateIterate₀ n f (f(x))

-- Accumulates the results of every step in `_^_` into a list.
-- Example:
--   accumulateIterate 0 f(x) = [x]
--   accumulateIterate 1 f(x) = [x , f(x)]
--   accumulateIterate 2 f(x) = [x , f(x) , f(f(x))]
--   accumulateIterate 3 f(x) = [x , f(x) , f(f(x)) , f(f(f(x)))]
--   accumulateIterate 4 f(x) = [x , f(x) , f(f(x)) , f(f(f(x))) , f(f(f(f(x))))]
accumulateIterate : (n : ℕ) → (T → T) → (T → List(T)(𝐒(n)))
accumulateIterate n = accumulateIterate₀(𝐒(n))
