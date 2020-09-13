module Numeral.CoordinateVector where

import      Lvl
open import Data.Boolean
open import Functional
open import Lang.Instance
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Finite.Oper
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Natural
import      Numeral.Natural.Oper as ℕ
open import Numeral.Natural.Function
open import Numeral.Natural.Function.Proofs
open import Type

private variable ℓ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable d d₁ d₂ : ℕ

-- Accessor of data in 1-dimensional finite space (Implies bounded).
-- Like a homogenous tuple or a fixed-size list.
-- The type is defined as the type of the vector projection function (A cell in the vector).
Vector : ℕ → Type{ℓ} → Type
Vector(d)(T) = 𝕟(d) → T

-- Type of elements in the vector
Element : Vector(d)(T) → Type
Element{T = T} = const T

-- The maximum number of dimensions of a space that the vector can describe points in
dim : Vector(d)(T) → ℕ
dim{d = d} = const d

-- The projection function (which also is the function itself).
proj : Vector(d)(T) → 𝕟(d) → T
proj = id

-- TODO: Move this to a separate "Relations" file
open import Logic
open import Relator.Equals.Proofs.Equivalence
open import Structure.Function.Domain
open import Structure.Setoid.WithLvl
private variable ℓₑ : Lvl.Level
-- The vector's elements are all distinct (the vector contains no duplicate elements).
Distinct : ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → Vector(d)(T) → Stmt
Distinct = Injective ⦃ [≡]-equiv ⦄

-- The first element of a non-empty vector
head : Vector(𝐒(d))(T) → T
head(v) = v(𝟎)

-- The list without the first element of a non-empty vector
tail : Vector(𝐒(d))(T) → Vector(d)(T)
(tail{𝟎}   (v)) ()
(tail{𝐒(_)}(v)) (i) = v(𝐒(i))

-- The list without the first element if there were any
tail₀ : Vector(d)(T) → Vector(Numeral.Natural.𝐏(d))(T)
tail₀{𝟎}    = id
tail₀{𝐒(_)} = tail

-- The last element of a non-empty vector
last : Vector(𝐒(d))(T) → T
last(v) = v(maximum)

-- The list without the last element if there were any
withoutLast : Vector(𝐒(d))(T) → Vector(d)(T)
(withoutLast v)(i) = v(bound-𝐒(i))

-- Applies a function on every value of the vector
map : (A → B) → Vector(d)(A) → Vector(d)(B)
(map f(v))(i) = f(v(i))

-- Applies a binary operation on every pair of values, each from 2 vectors elementwise
-- Example:
--   map₂(_+_) [1,2,3] [10,20,30] = [1+10 , 2+20 , 3+30] = [11,22,33]
map₂ : (A → B → C) → Vector(d)(A) → Vector(d)(B) → Vector(d)(C)
(map₂(_▫_) (v₁)(v₂))(i) = v₁(i) ▫ v₂(i)

map₂-min : (A → B → C) → ∀{d₁ d₂} → Vector(d₁)(A) → Vector(d₂)(B) → Vector(min d₁ d₂)(C)
(map₂-min(_▫_) (v₁)(v₂))(i) = v₁(bound-[≤] infer i) ▫ v₂(bound-[≤] infer i)

-- Example:
--   foldₗ (_▫_) (0) [1,2,3,4]
--   = (((0 ▫ 1) ▫ 2) ▫ 3) ▫ 4
foldₗ : (B → A → B) → B → Vector(d)(A) → B
foldₗ {d = 𝟎}    (_▫_) (init) (v) = init
foldₗ {d = 𝐒(d)} (_▫_) (init) (v) = foldₗ {d = d} (_▫_) (init ▫ (head v)) (tail v)

-- Example:
--   reduceₗ (_▫_) [1,2,3,4]
--   = ((1 ▫ 2) ▫ 3) ▫ 4
reduceₗ : (A → A → A) → Vector(𝐒(d))(A) → A
reduceₗ(_▫_) v = foldₗ(_▫_) (head v) (tail v)

-- Example:
--   reduceOrₗ (_▫_) 0 [1,2,3,4]
--   = ((1 ▫ 2) ▫ 3) ▫ 4
reduceOrₗ : (A → A → A) → A → Vector(d)(A) → A
reduceOrₗ {d = 𝟎}    _     empty _ = empty
reduceOrₗ {d = 𝐒(d)} (_▫_) empty v = foldₗ(_▫_) (head v) (tail v)

-- Example:
--   foldᵣ (_▫_) (0) [1,2,3,4]
--   = 1 ▫ (2 ▫ (3 ▫ (4 ▫ 0)))
foldᵣ : (A → B → B) → B → Vector(d)(A) → B
foldᵣ {d = 𝟎}    (_▫_) (init) (v) = init
foldᵣ {d = 𝐒(d)} (_▫_) (init) (v) = (head v) ▫ (foldᵣ {d = d} (_▫_) (init) (tail v))

-- Example:
--   foldᵣ-init (_▫_) (0) [1,2,3,4]
--   = 0 ▫ (1 ▫ (2 ▫ (3 ▫ 4)))
foldᵣ-init : (A → A → A) → A → Vector(d)(A) → A
foldᵣ-init {d = 𝟎}    (_▫_) (init) (v) = init
foldᵣ-init {d = 𝐒(d)} (_▫_) (init) (v) = init ▫ (foldᵣ-init {d = d} (_▫_) (head v) (tail v))

-- Example:
--   reduceᵣ (_▫_) [1,2,3,4]
--   = 1 ▫ (2 ▫ (3 ▫ 4))
reduceᵣ : (T → T → T) → Vector(𝐒(d))(T) → T
reduceᵣ {d = 𝟎}    (_▫_) (v) = head v
reduceᵣ {d = 𝐒(d)} (_▫_) (v) = (head v) ▫ (reduceᵣ (_▫_) (tail v))

-- Example:
--   reduceOrᵣ (_▫_) (0) [1,2,3,4]
--   = 1 ▫ (2 ▫ (3 ▫ 4))
reduceOrᵣ : (T → T → T) → T → Vector(d)(T) → T
reduceOrᵣ {d = 𝟎}    _     empty v = empty
reduceOrᵣ {d = 𝐒(d)} (_▫_) empty v = reduceᵣ(_▫_) v

-- A vector filled with multiple copies of a single element
fill : T → Vector(d)(T)
fill(elem) = const(elem)

-- An empty vector.
empty : Vector(𝟎)(T)
empty()

-- A vector with an additional element at the beginning
prepend : T → Vector(d)(T) → Vector(𝐒(d))(T)
(prepend(x)(_)) (𝟎)    = x
(prepend(_)(v)) (𝐒(n)) = v(n)

-- A vector concatenated with another vector
_++_ : Vector(d₁)(T) → Vector(d₂)(T) → Vector(d₁ ℕ.+ d₂)(T)
_++_ {d₁ = 𝟎}     {d₂ = d₂} v₁ v₂        = v₂
_++_ {d₁ = 𝐒(d₁)} {d₂ = d₂} v₁ v₂ (𝟎)    = v₁(𝟎)
_++_ {d₁ = 𝐒(d₁)} {d₂ = d₂} v₁ v₂ (𝐒(i)) = _++_ {d₁ = d₁} {d₂ = d₂} (v₁ ∘ 𝐒) v₂ i

count : (T → Bool) → Vector(d)(T) → ℕ
count {d = 𝟎}    (f)(v) = 𝟎
count {d = 𝐒(n)} (f)(v) =
  let next = count{d = n} (f)(tail v)
  in  if f(head v) then 𝐒(next) else next

reverse : Vector(d)(T) → Vector(d)(T)
(reverse(v)) (n) = v(Wrapping.[−] n)

indexProject : 𝕟(d) → T → T → Vector(d)(T)
indexProject n true false i = if(n ≡? i) then true else false

-- A vector without the element at the specified index
-- TODO: Implement Numeral.Finite.Bound.bound-𝐏
-- without : ∀{T}{d} → 𝕟(𝐒(d)) → Vector(𝐒(d))(T) → Vector(d)(T)
-- Vector.proj (without {_}{𝐒(_)} (𝟎)   (v)) (i) = Vector.proj(v)(𝐒(i))
-- Vector.proj (without {_}{𝐒(_)} (𝐒(n))(v)) (i) = if(i ≤? n) then Vector.proj(v)(𝐒(i)) else Vector.proj(v)(bound-𝐏(i))

-- postpend : ∀{T}{d} → T → Vector(d)(T) → Vector(𝐒(d))(T)
-- Vector.proj(postpend{_}{d} (x)(_)) (n) = if (n ≡? d) then x else Vector.proj(v)(n)

-- concat : ∀{T}{d₁ d₂} → Vector(d₁)(T) → Vector(d₂)(T) → Vector(d₁ + d₂)(T)
-- Vector.proj(concat(v₁)(v₂)) (n) with (n < d₁ ≡ 𝑇)
-- ... () = Vector.proj(v₁) (n)
-- ... () = Vector.proj(v₂) (n)

-- TODO: take / truncate
-- TODO: Equality by function equality
