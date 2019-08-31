module Data.ListSized where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Option as Option using (Option)
open import Functional
open import Numeral.FiniteStrict
open import Numeral.Natural
open import Numeral.Natural.Oper
-- open import Numeral.Natural.Oper.Proofs
open import Type

-- infixl 1000 _++_
infixr 1000 _⊰_
infixl 1      [_
infixl 100000 _]

-- A list is a container/collection with elements in order and which allows multiples
data List {ℓ} (T : Type{ℓ}) : ℕ → Type{ℓ} where
  ∅   : List(T)(𝟎) -- An empty list
  _⊰_ : ∀{n} → T → List(T)(n) → List(T)(𝐒(n)) -- Cons

pattern [_ l = l
pattern _] x = x ⊰ ∅

-- List concatenation
-- _++_ : ∀{ℓ}{T : Type{ℓ}}{a b} → List(T)(a) → List(T)(b) → List(T)(a + b)
-- _++_ ∅ b = b
-- _++_ (elem ⊰ rest) b = elem ⊰ (rest ++ b)

module LongOper where
  pattern empty = ∅
  pattern prepend elem list = elem ⊰ list
  -- concat   = _++_

module _ {ℓ} {T : Type{ℓ}} where
  -- The list with only a single element
  -- singleton : T → List(T)(1)
  -- singleton elem = elem ⊰ ∅
  pattern singleton x = x ⊰ ∅

  -- The first element of the list
  head : ∀{n} → List(T)(𝐒(n)) → T
  head (x ⊰ _) = x

  -- The list without its first element
  tail : ∀{n} → List(T)(𝐒(n)) → List(T)(n)
  tail (_ ⊰ l) = l

  -- The nth element in the list
  index : ∀{n} → 𝕟(n) → List(T)(n) → T
  index 𝟎      (x ⊰ _) = x
  index (𝐒(n)) (_ ⊰ l) = index n l

  -- The sublist with the first n elements in the list
  first : ∀{n} → (k : 𝕟₌(n)) → List(T)(n) → List(T)(𝕟-to-ℕ k)
  first 𝟎      _       = ∅
  first (𝐒(n)) (x ⊰ l) = x ⊰ (first n l)

  -- skip : ∀{n} → (k : 𝕟₌(n)) → List(T)(n) → List(T)(n − k)
  -- last : ∀{n} → (k : 𝕟₌(n)) → List(T)(n) → List(T)(𝕟-to-ℕ k)

  -- Length of the list (number of elements in the list)
  length : ∀{n} → List(T)(n) → ℕ
  length {n} _ = n

  -- The list with an element repeated n times
  repeat : T → (n : ℕ) → List(T)(n)
  repeat _ 𝟎      = ∅
  repeat x (𝐒(n)) = x ⊰ (repeat x n)

  -- A list constructed from a function
  -- fromFn : ∀{n} → (𝕟(n) → T) → List(T)(n)
  -- fromFn {𝟎}    _ = ∅
  -- fromFn {𝐒(n)} f = f(𝟎) ⊰ fromFn {n} (f ∘ 𝐏₀)

  -- The list with a list concatenated (repeated) n times
  -- _++^_ : ∀{n} → List(T) → (k : ℕ) → List(T)(k ⋅ n)
  -- _++^_ _ 𝟎      = ∅
  -- _++^_ l (𝐒(n)) = l ++ (l ++^ n)

module _ {ℓ₁}{ℓ₂} where
  -- Applies a function to each element in the list
  map : ∀{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}}{n} → (T₁ → T₂) → List(T₁)(n) → List(T₂)(n)
  map _ ∅ = ∅
  map f (elem ⊰ l) = (f elem) ⊰ (map f l)

  -- Applies a binary operator to each element in the list starting with the initial element.
  -- Example:
  --   foldₗ(▫)(init)[]          = init
  --   foldₗ(▫)(init)[a]         = init▫a
  --   foldₗ(▫)(init)[a,b]       = (init▫a)▫b
  --   foldₗ(▫)(init)[a,b,c,d,e] = ((((init▫a)▫b)▫c)▫d)▫e
  foldₗ : ∀{T : Type{ℓ₁}}{Result : Type{ℓ₂}}{n} → (Result → T → Result) → Result → List(T)(n) → Result
  foldₗ _   result ∅ = result
  foldₗ _▫_ result (elem ⊰ l) = foldₗ _▫_ (result ▫ elem) l

  -- Applies a binary operator to each element in the list starting with the initial element.
  -- Example:
  --   foldᵣ(▫)(init)[]          = init
  --   foldᵣ(▫)(init)[a]         = a▫init
  --   foldᵣ(▫)(init)[a,b]       = a▫(b▫init)
  --   foldᵣ(▫)(init)[a,b,c,d,e] = a▫(b▫(c▫(d▫(e▫init))))
  foldᵣ : ∀{T : Type{ℓ₁}}{Result : Type{ℓ₂}}{n} → (T → Result → Result) → Result → List(T)(n) → Result
  foldᵣ _   init ∅ = init
  foldᵣ _▫_ init (elem ⊰ l) = elem ▫ (foldᵣ _▫_ init l)

module _ {ℓ} {T : Type{ℓ}} where
  -- Example:
  --   reduceₗ(▫)[a]         = a
  --   reduceₗ(▫)[a,b]       = a▫b
  --   reduceₗ(▫)[a,b,c]     = (a▫b)▫c
  --   reduceₗ(▫)[a,b,c,d,e] = (((a▫b)▫c)▫d)▫e
  reduceₗ : ∀{n} → (T → T → T) → List(T)(𝐒(n)) → T
  reduceₗ _▫_ (elem ⊰ l) = foldₗ _▫_ elem l

  -- Example:
  --   reduceᵣ(▫)[a]         = a
  --   reduceᵣ(▫)[a,b]       = a▫b
  --   reduceᵣ(▫)[a,b,c]     = a▫(b▫c)
  --   reduceᵣ(▫)[a,b,c,d,e] = a▫(b▫(c▫(d▫e)))
  reduceᵣ : ∀{n} → (T → T → T) → List(T)(𝐒(n)) → T
  reduceᵣ _▫_ (elem ⊰ l) = foldᵣ _▫_ elem l
