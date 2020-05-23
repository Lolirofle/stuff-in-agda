module Data.Tuple.Raiseᵣ.Functions where

open import Data
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Raiseᵣ
open import Numeral.Natural
open import Numeral.Natural.Oper using (_+_ ; _⋅_)
open import Numeral.Natural.Oper.Proofs
open import Numeral.Finite
open import Syntax.Number
open import Type

module _ {ℓ} {T : Type{ℓ}} where
  -- Prepends an element to a tuple.
  -- Example: a ⊰ (b,c) = (a,b,c)
  _⊰_ : ∀{n : ℕ} → T → (T ^ n) → (T ^ 𝐒(n))
  _⊰_ {𝟎}       x _ = x
  _⊰_ {𝐒(n)}    x l = (x , l)

  -- The first element of a tuple.
  -- Example: head(a,b,c) = a
  head : ∀{n : ℕ} → (T ^ (𝐒(n))) → T
  head {𝟎}    x       = x
  head {𝐒(_)} (x , _) = x

  -- The tuple without its first element.
  -- Example: tail(a,b,c) = (b,c)
  tail : ∀{n : ℕ} → (T ^ (𝐒(n))) → (T ^ n)
  tail {𝟎}    _       = <>
  tail {𝐒(_)} (_ , x) = x

-- Example: map f(a,b,c,d) = (f(a),f(b),f(c),f(d))
map : ∀{n : ℕ}{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → B) → ((A ^ n) → (B ^ n))
map {0}       f _ = <>
map {1}       f single        = f(single)
map {𝐒(𝐒(n))} f (init , rest) = (f(init) , map{𝐒(n)} f rest)

-- Example: map₂(_▫_) (a₁,b₁,c₁,d₁) (a₂,b₂,c₂,d₂) = (a₁ ▫ a₂ , b₁ ▫ b₂ , c₁ ▫ c₂ , d₁ ▫ d₂)
map₂ : ∀{n : ℕ}{ℓ₁ ℓ₂ ℓ}{A₁ : Type{ℓ₁}}{A₂ : Type{ℓ₂}}{B : Type{ℓ}} → (A₁ → A₂ → B) → ((A₁ ^ n) → (A₂ ^ n) → (B ^ n))
map₂ {0}       _ _        _        = <>
map₂ {1}       f x        y        = f x y
map₂ {𝐒(𝐒(n))} f (x , xs) (y , ys) = (f x y , map₂{𝐒(n)} f xs ys)

-- Transposes two tuples of the same length to one tuple of tuples containing the pairs.
zip : ∀{n : ℕ}{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (T₁ ^ n) → (T₂ ^ n) → ((T₁ ⨯ T₂) ^ n)
zip {0}       <>        <>        = <>
zip {1}       a         b         = (a , b)
zip {𝐒(𝐒(n))} (ah , at) (bh , bt) = ((ah , bh) , zip {𝐒(n)} at bt)

-- Returns a element repeated a specified number of times in a tuple
repeat : ∀{ℓ}{T : Type{ℓ}} → (n : _) → T → (T ^ n)
repeat(0)       _ = <>
repeat(1)       x = x
repeat(𝐒(𝐒(n))) x = (x , repeat(𝐒(n)) x)

-- Example: reduceᵣ(_▫_) (a,b,c,d) = a ▫ (b ▫ (c ▫ d))
reduceᵣ : ∀{n : ℕ}{ℓ}{T : Type{ℓ}} → (T → T → T) → (T ^ 𝐒(n)) → T
reduceᵣ {𝟎}    (_▫_) x        = x
reduceᵣ {𝐒(n)} (_▫_) (x , xs) = x ▫ reduceᵣ {n} (_▫_) xs

-- Example: foldᵣ(_▫_) def (a,b,c,d) = a ▫ (b ▫ (c ▫ (d ▫ def)))
foldᵣ : ∀{n : ℕ}{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → B → B) → B → (A ^ n) → B
foldᵣ {0}       (_▫_) def _        = def
foldᵣ {1}       (_▫_) def x        = x ▫ def
foldᵣ {𝐒(𝐒(n))} (_▫_) def (x , xs) = x ▫ foldᵣ {𝐒(n)} (_▫_) def xs

-- Example: reduceOrᵣ(_▫_) def (a,b,c,d) = a ▫ (b ▫ (c ▫ d))
reduceOrᵣ : ∀{n : ℕ}{ℓ}{A : Type{ℓ}} → (A → A → A) → A → (A ^ n) → A
reduceOrᵣ {0}       (_▫_) def _        = def
reduceOrᵣ {1}       (_▫_) def x        = x
reduceOrᵣ {𝐒(𝐒(n))} (_▫_) def (x , xs) = x ▫ reduceOrᵣ {𝐒(n)} (_▫_) def xs

-- TODO: Could be split to an implementation of something of type "(A ^ n) → A ^ (min 1 n)" or "(A ^ n) → (A ^ S(P(n)))" instead, or maybe reduceOrᵣ
mapReduceᵣ : ∀{n : ℕ}{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → A → A) → B → (A → B) → (A ^ n) → B
mapReduceᵣ {𝟎}       (_▫_) def map _ = def
mapReduceᵣ {𝐒(n)}    (_▫_) def map l = map(reduceᵣ {n} (_▫_) l)

-- Example: foldₗ(_▫_) def (a,b,c,d) = (((def ▫ a) ▫ b) ▫ c) ▫ d
foldₗ : ∀{n : ℕ}{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (B → A → B) → B → (A ^ n) → B
foldₗ {0}       (_▫_) def _        = def
foldₗ {1}       (_▫_) def x        = def ▫ x
foldₗ {𝐒(𝐒(n))} (_▫_) def (x , xs) = foldₗ {𝐒(n)} (_▫_) (def ▫ x) xs

module _ {ℓ} {T : Type{ℓ}} where
  -- A tuple with only a single element.
  -- Example: singelton(x) = x
  singleton : T → (T ^ 1)
  singleton(x) = x

  -- The element at the specified position of a tuple (allowing out of bounds positions).
  -- If the position is out of bounds (greater than the length of the tuple), then the last element is returned.
  -- Examples:
  --   index(0)(a,b,c,d) = a
  --   index(1)(a,b,c,d) = b
  --   index(2)(a,b,c,d) = c
  --   index(3)(a,b,c,d) = d
  --   index(4)(a,b,c,d) = d
  --   index(5)(a,b,c,d) = d
  index₀ : ∀{n : ℕ} → ℕ → (T ^ (𝐒(n))) → T
  index₀ {𝟎}    _      x          = x
  index₀ {𝐒(_)} 𝟎      (init , _) = init
  index₀ {𝐒(n)} (𝐒(i)) (_ , rest) = index₀{n}(i)(rest)

  -- The element at the specified position of a tuple.
  -- Example: index(2)(a,b,c,d) = c
  index : ∀{n : ℕ} → 𝕟(n) → (T ^ n) → T
  index {0}       ()
  index {1}       𝟎      x          = x
  index {𝐒(𝐒(_))} 𝟎      (init , _) = init
  index {𝐒(𝐒(n))} (𝐒(i)) (_ , rest) = index{𝐒(n)}(i)(rest)

  -- The tuple without the element at the specified position.
  -- Example: without(2)(a,b,c,d) = (a,b,d)
  without : ∀{n : ℕ} → 𝕟(𝐒(n)) → (T ^ 𝐒(n)) → (T ^ n)
  without {𝟎}    𝟎     _        = <>
  without {𝐒(n)} 𝟎     (x₁ , l) = l
  without {𝐒(n)} (𝐒 i) (x₁ , l) = (x₁ ⊰ without {n} i l)

  -- Concatenates two tuples.
  -- Example: (1,2,3,4) ++ (5,6) = (1,2,3,4,5,6)
  _++_ : ∀{a b : ℕ} → (T ^ a) → (T ^ b) → (T ^ (a + b))
  _++_ {a = 0}       _        ys = ys
  _++_ {a = 1}       x        ys = x ⊰ ys
  _++_ {a = 𝐒(𝐒(a))} (x , xs) ys = x ⊰ (xs ++ ys)

  -- Concatenates all tuples in the specified tuple of tuples.
  -- Example: concat((1,2,3),(4,5,6)) = (1,2,3,4,5,6)
  concat : ∀{a b : ℕ} → ((T ^ a) ^ b) → (T ^ (a ⋅ b))
  concat {b = 0}       _          = <>
  concat {b = 1}       xs         = xs
  concat {b = 𝐒(𝐒(b))} (xs , xss) = xs ++ concat {b = 𝐒(b)} xss

  -- Transposes the specified tuple of tuples.
  -- Example: transpose((1,(2,3)),(4,(5,6)),(7,(8,9))) = (((1,(4,7)),(2,(5,8)),(3,(6,9))))
  transpose : ∀{m n : ℕ} → ((T ^ m) ^ n) → ((T ^ n) ^ m)
  transpose {n}       {0}       <>       = repeat n <>
  transpose {_}       {1}       x        = x
  transpose {m}       {𝐒(𝐒(n))} (x , xs) = zip{m} x (transpose {m} {𝐒(n)} xs)
