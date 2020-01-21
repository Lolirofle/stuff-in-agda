module Data.Tuple.Raiseᵣ where

open import Data
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Numeral.Natural
open import Numeral.Natural.Oper using (_+_ ; _⋅_)
open import Numeral.Natural.Oper.Proofs
open import Numeral.Finite
open import Syntax.Number
open import Type

_^_ : ∀{ℓ} → Type{ℓ} → ℕ → Type{ℓ}
_^_ type 0      = Unit
_^_ type 1      = type
_^_ type (𝐒(𝐒(n))) = type ⨯ (type ^ 𝐒(n))

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

-- Returns a multivariate function from a singlevariate function
lift : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (n : _) → (A → B) → ((A ^ n) → (B ^ n))
lift(0)       f(_)  = <>
lift(1)       f(x)  = f(x)
lift(𝐒(𝐒(n))) f(first , rest) = (f(first) , lift(𝐒(n)) f(rest))

-- Example: reduceᵣ(_▫_) (a,b,c,d) = a ▫ (b ▫ (c ▫ d))
reduceᵣ : ∀{n : ℕ}{ℓ}{T : Type{ℓ}} → (T → T → T) → (T ^ 𝐒(n)) → T
reduceᵣ {𝟎}    (_▫_) x        = x
reduceᵣ {𝐒(n)} (_▫_) (x , xs) = x ▫ reduceᵣ {n} (_▫_) xs

-- Example: foldᵣ(_▫_) def (a,b,c,d) = a ▫ (b ▫ (c ▫ (d ▫ def)))
foldᵣ : ∀{n : ℕ}{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → B → B) → B → (A ^ n) → B
foldᵣ {𝟎}       (_▫_) def _        = def
foldᵣ {𝐒(𝟎)}    (_▫_) def x        = x ▫ def
foldᵣ {𝐒(𝐒(n))} (_▫_) def (x , xs) = x ▫ foldᵣ {𝐒(n)} (_▫_) def xs

-- TODO: Could be split to an implementation of something of type "(A ^ n) → A ^ (min 1 n)" or "(A ^ n) → (A ^ S(P(n)))" instead
mapReduceᵣ : ∀{n : ℕ}{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → A → A) → B → (A → B) → (A ^ n) → B
mapReduceᵣ {𝟎}       (_▫_) def map _ = def
mapReduceᵣ {𝐒(n)}    (_▫_) def map l = map(reduceᵣ {n} (_▫_) l)

-- Example: foldₗ(_▫_) def (a,b,c,d) = (((def ▫ a) ▫ b) ▫ c) ▫ d
foldₗ : ∀{n : ℕ}{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (B → A → B) → B → (A ^ n) → B
foldₗ {𝟎}       (_▫_) def _        = def
foldₗ {𝐒(𝟎)}    (_▫_) def x        = def ▫ x
foldₗ {𝐒(𝐒(n))} (_▫_) def (x , xs) = foldₗ {𝐒(n)} (_▫_) (def ▫ x) xs

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

  -- A tuple with only a single element.
  -- Example: singelton(x) = x
  singleton : ∀{n : ℕ} → T → (T ^ 1)
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
  index {𝟎}       ()
  index {𝐒(𝟎)}    𝟎      x          = x
  index {𝐒(𝐒(_))} 𝟎      (init , _) = init
  index {𝐒(𝐒(n))} (𝐒(i)) (_ , rest) = index{𝐒(n)}(i)(rest)

  -- The tuple without the element at the specified position.
  -- Example: without(2)(a,b,c,d) = (a,b,d)
  without : ∀{n : ℕ} → 𝕟(𝐒(n)) → (T ^ 𝐒(n)) → (T ^ n)
  without {0}       𝟎     _ = <>
  without {𝐒(n)} 𝟎     (x₁ , l) = l
  without {𝐒(n)} (𝐒 i) (x₁ , l) = (x₁ ⊰ without {n} i l)

  -- Concatenates two tuples.
  -- Example: (1,2,3,4) ++ (5,6) = (1,2,3,4,5,6)
  _++_ : ∀{a b : ℕ} → (T ^ a) → (T ^ b) → (T ^ (a + b))
  _++_ {a = 𝟎}       _        ys = ys
  _++_ {a = 𝐒(𝟎)}    x        ys = x ⊰ ys
  _++_ {a = 𝐒(𝐒(a))} (x , xs) ys = x ⊰ (xs ++ ys)

  -- Concatenates all tuples in the specified tuple of tuples.
  -- Example: concat((1,2,3),(4,5,6)) = (1,2,3,4,5,6)
  concat : ∀{a b : ℕ} → ((T ^ a) ^ b) → (T ^ (a ⋅ b))
  concat {b = 𝟎}       _          = <>
  concat {b = 𝐒(𝟎)}    xs         = xs
  concat {b = 𝐒(𝐒(b))} (xs , xss) = xs ++ concat {b = 𝐒(b)} xss

  -- Transposes the specified tuple of tuples.
  -- Example: transpose((1,(2,3)),(4,(5,6)),(7,(8,9))) = (((1,(4,7)),(2,(5,8)),(3,(6,9))))
  transpose : ∀{m n : ℕ} → ((T ^ m) ^ n) → ((T ^ n) ^ m)
  transpose {n}       {0}       <>       = repeat n <>
  transpose {_}       {1}       x        = x
  transpose {m}       {𝐒(𝐒(n))} (x , xs) = zip{m} x (transpose {m} {𝐒(n)} xs)
