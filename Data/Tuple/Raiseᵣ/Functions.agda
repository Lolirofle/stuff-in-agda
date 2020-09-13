module Data.Tuple.Raiseᵣ.Functions where

import      Lvl
open import Data hiding (empty)
open import Data.Option as Option using (Option)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Raiseᵣ
open import Functional using (id ; const ; apply)
open import Functional.Dependent using (_∘_)
open import Numeral.Natural
open import Numeral.Natural.Oper using (_+_ ; _⋅_)
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Finite
open import Syntax.Function
open import Syntax.Number
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A B A₁ A₂ : Type{ℓ}
private variable n n₁ n₂ : ℕ

-------------------------------------------------------------------------------
-- Primitives

-- Prepends an element to a tuple.
-- Example: a ⊰ (b,c) = (a,b,c)
_⊰_ : let _ = n in T → (T ^ n) → (T ^ 𝐒(n))
_⊰_ {𝟎}    = const
_⊰_ {𝐒(n)} = _,_
prepend = _⊰_

elim : ∀{P : ∀(n) → (T ^ n) → Type{ℓ}} → P(𝟎)(<>) → (∀(x) → P(𝐒(𝟎))(x)) → (∀{n}(x)(l) → P(𝐒(n))(l) → P(𝐒(𝐒(n)))(x , l)) → (∀{n}(l) → P(n)(l))
elim        p₀ _  _  {0}       <>      = p₀
elim        _  p₁ _  {1}       x       = p₁ x
elim{P = P} p₀ p₁ p₊ {𝐒(𝐒(n))} (x , l) = p₊ x l (elim{P = P} p₀ p₁ p₊ {𝐒(n)} l)

-------------------------------------------------------------------------------
-- Derivations from the primitives

elim₊ : ∀{P : ∀(n) → (T ^ 𝐒(n)) → Type{ℓ}} → (∀(x) → P(𝟎)(x)) → (∀{n}(x)(l) → P(n)(l) → P(𝐒(n))(x , l)) → (∀{n}(l) → P(n)(l))
elim₊{T = T}{P = P} p₁ p₊ {n} l = elim{P = P₀} <> p₁ p₊ {𝐒(n)} l where
  P₀ : ∀(n : ℕ) → (T ^ n) → Type
  P₀ 𝟎     = const Unit
  P₀ (𝐒 n) = P(n)

elimIndepOp : ∀{P : ℕ → Type{ℓ}} → P(𝟎) → (∀{n} → T → P(n) → P(𝐒(n))) → (∀{n} → (T ^ n) → P(n))
elimIndepOp{P = P} p₀ p₊ {n} l = elim{P = const ∘ P} p₀ (apply p₀ ∘ p₊) (const ∘ p₊) {n} l

-- Example: reduceᵣ(_▫_) (a,b,c,d) = a ▫ (b ▫ (c ▫ d))
-- Alternative implementation:
--   reduceᵣ {𝟎}    (_▫_) x        = x
--   reduceᵣ {𝐒(n)} (_▫_) (x , xs) = x ▫ reduceᵣ {n} (_▫_) xs
reduceᵣ : let _ = n in (T → T → T) → (T ^ 𝐒(n)) → T
reduceᵣ(_▫_) = elim₊ id (const ∘ (_▫_))

-- Example: foldᵣ(_▫_) def (a,b,c,d) = a ▫ (b ▫ (c ▫ (d ▫ def)))
-- Alternative implementation:
--   foldᵣ {0}       (_▫_) def _        = def
--   foldᵣ {1}       (_▫_) def x        = x ▫ def
--   foldᵣ {𝐒(𝐒(n))} (_▫_) def (x , xs) = x ▫ foldᵣ {𝐒(n)} (_▫_) def xs
foldᵣ : let _ = n in (A → B → B) → B → (A ^ n) → B
foldᵣ(_▫_) id = elimIndepOp id (_▫_)

-- Example: reduceOrᵣ(_▫_) def (a,b,c,d) = a ▫ (b ▫ (c ▫ d))
-- Alternative implementation:
--   reduceOrᵣ {0}       (_▫_) def _        = def
--   reduceOrᵣ {1}       (_▫_) def x        = x
--   reduceOrᵣ {𝐒(𝐒(n))} (_▫_) def (x , xs) = x ▫ reduceOrᵣ {𝐒(n)} (_▫_) def xs
reduceOrᵣ : let _ = n in (A → A → A) → A → (A ^ n) → A
reduceOrᵣ{n} (_▫_) def = elim def id (const ∘ (_▫_)) {n}

-- Postpends an element to a tuple.
-- Example: postpend c (a,b) = (a,b,c)
-- Alternative implementation:
--   postpend {0}       a _       = a
--   postpend {1}       a x       = (x , a)
--   postpend {𝐒(𝐒(n))} a (x , l) = (x , postpend {n = 𝐒(n)} a l)
postpend : let _ = n in T → (T ^ n) → (T ^ (𝐒(n)))
postpend{T = T} a = elimIndepOp{P = (T ^_) ∘ 𝐒} a prepend

-- Example: map f(a,b,c,d) = (f(a),f(b),f(c),f(d))
-- Alternative implementation:
--   map {0}       f _ = <>
--   map {1}       f single        = f(single)
--   map {𝐒(𝐒(n))} f (init , rest) = (f(init) , map{𝐒(n)} f rest)
map : let _ = n in (A → B) → ((A ^ n) → (B ^ n))
map f = elimIndepOp{P = _ ^_} <> (prepend ∘ f)

-------------------------------------------------------------------------------
-- Construction from other stuff

-- An empty tuple.
-- Example: empty = <>
empty : (T ^ 0)
empty = <>

-- A tuple with only a single element.
-- Example: singleton(x) = x
singleton : T → (T ^ 1)
singleton = id

-- Returns a element repeated a specified number of times in a tuple
repeat : (n : _) → T → (T ^ n)
repeat(0)       _ = <>
repeat(1)       x = x
repeat(𝐒(𝐒(n))) x = (x , repeat(𝐒(n)) x)

-------------------------------------------------------------------------------
-- Other

{-
intro : (n : ℕ) → ((i : ℕ) ⦃ ord : i < n ⦄ → (T ^ i) → T) → (T ^ n)
intro 0         _ = <>
intro 1         f = f(𝟎) <>
intro (𝐒(𝐒(n))) f =
  let rest = intro (𝐒(n)) (\i ⦃ ord ⦄ → f(i) ⦃ [≤]-successor ord ⦄)
  in  (f(𝐒(n)) ⦃ [<]-of-[𝐒] ⦄ rest , rest)
-}

-- Example: foldₗ(_▫_) def (a,b,c,d) = (((def ▫ a) ▫ b) ▫ c) ▫ d
foldₗ : let _ = n in (B → A → B) → B → (A ^ n) → B
foldₗ {0}       (_▫_) def _        = def
foldₗ {1}       (_▫_) def x        = def ▫ x
foldₗ {𝐒(𝐒(n))} (_▫_) def (x , xs) = foldₗ {𝐒(n)} (_▫_) (def ▫ x) xs

-- TODO: Could be split to an implementation of something of type "(A ^ n) → A ^ (min 1 n)" or "(A ^ n) → (A ^ S(P(n)))" instead, or maybe reduceOrᵣ
mapReduceᵣ : let _ = n in (A → A → A) → B → (A → B) → (A ^ n) → B
mapReduceᵣ {𝟎}       (_▫_) def map _ = def
mapReduceᵣ {𝐒(n)}    (_▫_) def map l = map(reduceᵣ {n} (_▫_) l)

-- Example: map₂(_▫_) (a₁,b₁,c₁,d₁) (a₂,b₂,c₂,d₂) = (a₁ ▫ a₂ , b₁ ▫ b₂ , c₁ ▫ c₂ , d₁ ▫ d₂)
map₂ : let _ = n in (A₁ → A₂ → B) → ((A₁ ^ n) → (A₂ ^ n) → (B ^ n))
map₂ {0}       _ _        _        = <>
map₂ {1}       f x        y        = f x y
map₂ {𝐒(𝐒(n))} f (x , xs) (y , ys) = (f x y , map₂{𝐒(n)} f xs ys)

-- Transposes two tuples of the same length to one tuple of tuples containing the pairs.
zip : let _ = n in (A ^ n) → (B ^ n) → ((A ⨯ B) ^ n)
zip {0}       <>        <>        = <>
zip {1}       a         b         = (a , b)
zip {𝐒(𝐒(n))} (ah , at) (bh , bt) = ((ah , bh) , zip {𝐒(n)} at bt)

-- The first element of a tuple.
-- Example: head(a,b,c) = a
head : let _ = n in (T ^ (𝐒(n))) → T
head {𝟎}    x       = x
head {𝐒(_)} (x , _) = x

-- The tuple without its first element.
-- Example: tail(a,b,c) = (b,c)
tail : let _ = n in (T ^ (𝐒(n))) → (T ^ n)
tail {𝟎}    _       = <>
tail {𝐒(_)} (_ , x) = x

head₀ : let _ = n in (T ^ n) → Option(T)
head₀ {𝟎}    _ = Option.None
head₀ {𝐒(n)} l = Option.Some(head l)

-- The element at the specified position of a tuple (allowing out of bounds positions).
-- If the position is out of bounds (greater than the length of the tuple), then the last element is returned.
-- Examples:
--   index(0)(a,b,c,d) = a
--   index(1)(a,b,c,d) = b
--   index(2)(a,b,c,d) = c
--   index(3)(a,b,c,d) = d
--   index(4)(a,b,c,d) = d
--   index(5)(a,b,c,d) = d
index₀ : let _ = n in ℕ → (T ^ (𝐒(n))) → T
index₀ {𝟎}    _      x          = x
index₀ {𝐒(_)} 𝟎      (init , _) = init
index₀ {𝐒(n)} (𝐒(i)) (_ , rest) = index₀{n}(i)(rest)

-- The element at the specified position of a tuple.
-- Example: index(2)(a,b,c,d) = c
index : let _ = n in 𝕟(n) → (T ^ n) → T
index {0}       ()
index {1}       𝟎      x          = x
index {𝐒(𝐒(_))} 𝟎      (init , _) = init
index {𝐒(𝐒(n))} (𝐒(i)) (_ , rest) = index{𝐒(n)}(i)(rest)

-- The tuple without the element at the specified position.
-- Example: without(2)(a,b,c,d) = (a,b,d)
without : let _ = n in 𝕟(𝐒(n)) → (T ^ 𝐒(n)) → (T ^ n)
without {𝟎}    𝟎     _        = <>
without {𝐒(n)} 𝟎     (x₁ , l) = l
without {𝐒(n)} (𝐒 i) (x₁ , l) = (x₁ ⊰ without {n} i l)

updateAt : let _ = n in 𝕟(n) → (T → T) → (T ^ n) → (T ^ n)
updateAt {1}       𝟎     f x       = f(x)
updateAt {𝐒(𝐒(n))} 𝟎     f (x , l) = (f(x) , l)
updateAt {𝐒(𝐒(n))} (𝐒 i) f (x , l) = (x , updateAt{𝐒(n)} i f l)

-- Concatenates two tuples.
-- Example: (1,2,3,4) ++ (5,6) = (1,2,3,4,5,6)
_++_ : let _ = n₁ ; _ = n₂ in (T ^ n₁) → (T ^ n₂) → (T ^ (n₁ + n₂))
_++_ {0}        _        ys = ys
_++_ {1}        x        ys = x ⊰ ys
_++_ {𝐒(𝐒(n₁))} (x , xs) ys = x ⊰ (_++_ {𝐒(n₁)} xs ys)

-- Concatenates all tuples in the specified tuple of tuples.
-- Example: concat((1,2,3),(4,5,6)) = (1,2,3,4,5,6)
concat : let _ = n₁ ; _ = n₂ in ((T ^ n₁) ^ n₂) → (T ^ (n₁ ⋅ n₂))
concat {_} {0}        _          = <>
concat {_} {1}        xs         = xs
concat {n₁}{𝐒(𝐒(n₂))} (xs , xss) = _++_ {n₁}{n₁ ⋅ 𝐒(n₂)} xs (concat {n₁}{𝐒(n₂)} xss)

-- Transposes the specified tuple of tuples.
-- Example: transpose((1,(2,3)),(4,(5,6)),(7,(8,9))) = (((1,(4,7)),(2,(5,8)),(3,(6,9))))
transpose : let _ = n₁ ; _ = n₂ in ((T ^ n₁) ^ n₂) → ((T ^ n₂) ^ n₁)
transpose {n₁}       {0}        <>       = repeat n₁ <>
transpose {_}        {1}        x        = x
transpose {n₁}       {𝐒(𝐒(n₂))} (x , xs) = zip{n₁} x (transpose {n₁} {𝐒(n₂)} xs)
