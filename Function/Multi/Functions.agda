module Function.Multi.Functions where

open import Data
open import Data.Tuple renaming (curry to curry₁ ; uncurry to uncurry₁) using (_⨯_ ; _,_)
open import Data.Tuple.Raise
import      Data.Tuple.Raiseᵣ.Functions as Raise
open import Data.Tuple.RaiseTypeᵣ
open import Data.Tuple.RaiseTypeᵣ.Functions
open import Function.Multi
open import Functional using (_→ᶠ_ ; id ; _∘_ ; _⦗_⦘_) renaming (const to const₁ ; apply to apply₁ ; swap to swap₁ ; _$_ to _$₁_)
open import Logic
import      Lvl
import      Lvl.MultiFunctions as Lvl
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Natural
open import Syntax.Function
open import Syntax.Number
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ : Lvl.Level
private variable n n₁ n₂ : ℕ
private 
  module _ {n : ℕ} where
    variable ℓ𝓈 ℓ𝓈₁ ℓ𝓈₂ : Lvl.Level ^ n

-- A constant function of many variables.
-- Lifts a value to being a number of nested functions.
-- Examples:
--   const(x) _ _ _ ... = x
--   const(x)
--   = (const₁ ∘ const₁ ∘ const₁ ∘ ...)(x)
--   = (_ ↦ (_ ↦ (_ ↦ x)))
--   = (_ ↦ _ ↦ _ ↦ x)
const : ∀{As : Types{n}(ℓ𝓈)}{B : Type{ℓ}} → B → (As ⇉ B)
const {n = 𝟎}       = id
const {n = 𝐒(𝟎)}    = const₁
const {n = 𝐒(𝐒(n))} = const₁ ∘ const

-- A projection function of many variables.
-- Returns one of the specified arguments.
-- Examples:
--   proj(0) x y = x
--   proj(1) x y = y
--   proj(0) x y z = x
--   proj(1) x y z = y
--   proj(2) x y z = z
--   proj(0) x y z w = x
--   proj(1) x y z w = y
--   proj(2) x y z w = z
--   proj(3) x y z w = w
proj : ∀{As : Types{n}(ℓ𝓈)} → (i : 𝕟(n)) → (As ⇉ index i As)
proj {n = 𝐒(𝟎)}    𝟎      x = x
proj {n = 𝐒(𝐒(n))} 𝟎      x = const x
proj {n = 𝐒(𝐒(n))} (𝐒(i)) _ = proj i

-- Applies a function on the return value of a multivariate function.
-- Composes the first argument and the last function of the second argument.
-- Can also be seen as lifting the function type to the structure of (As ⇉_).
-- Examples:
--   f ∘ᵣ g = (((f ∘_) ∘_) ∘_) ..
--   ((((f ∘ᵣ g) x₁) x₂) x₃) .. = f((((g x₁) x₂) x₃) ..)
--   (f ∘ᵣ g) x₁ x₂ x₃ .. = f(g x₁ x₂ x₃ ..)
-- Note: This can be used to specify the `map` function of a functor (As ⇉_).
_∘ᵣ_ : ∀{As : Types{n}(ℓ𝓈)}{B : Type{ℓ₁}}{C : Type{ℓ₂}} → (B → C) → (As ⇉ B) → (As ⇉ C)
_∘ᵣ_ {n = 𝟎}         = id
_∘ᵣ_ {n = 𝐒(𝟎)}      = _∘_
_∘ᵣ_ {n = 𝐒(𝐒(n))} f = (f ∘ᵣ_) ∘_

-- Converts a function using a tuple to represent its arguments to a curried function (nested function types).
-- Example:
--   curry((x,y,z,...) ↦ φ) = (x ↦ y ↦ z ↦ ... ↦ φ)
-- Note: If there is a nested uncurry and curry, one can often rewrite it using (_∘ᵣ_) instead (I think).
-- Note:
--   curry                 : ((a₁ , a₂) -> b) -> a₁ -> a₂ -> b
--   curry ∘ curry         : (((a₁ , a₂), a₃) -> b) -> a₁ -> a₂ -> a₃ -> b
--   curry ∘ curry ∘ curry : ((((a₁ , a₂) , a₃) , a₄) -> b) -> a₁ -> a₂ -> a₃ -> a₄ -> b
curry : ∀{As : Types{𝐒(n)}(ℓ𝓈)}{B : Type{ℓ}} → (reduceᵣ(_⨯_) As → B) → (As ⇉ B)
curry {n = 𝟎}        = id
curry {n = 𝐒(n)} f x = curry {n = n} (f ∘ (x ,_))

-- Converts a curried function (nested function types) to a function using a tuple to represent its arguments.
-- Example:
--   uncurry(x ↦ y ↦ z ↦ ... ↦ φ) = ((x,y,z,...) ↦ φ)
uncurry : ∀{As : Types{𝐒(n)}(ℓ𝓈)}{B : Type{ℓ}} → (As ⇉ B) → (reduceᵣ(_⨯_) As → B)
uncurry {n = 𝟎}               = id
uncurry {n = 𝐒(n)} f (x , xs) = uncurry {n = n} (f(x)) xs

-- Applies a tuple as arguments to a multivariate function.
-- Example:
--   apply(x,y,z,...) (x ↦ y ↦ z ↦ ... ↦ φ) = φ
apply : ∀{As : Types{𝐒(n)}(ℓ𝓈)}{B : Type{ℓ}} → (reduceᵣ(_⨯_) As) → (As ⇉ B) → B
apply = swap₁ uncurry

_$_ = uncurry

-- Applies an argument to a specific position in the arguments of an argument list of a multivariate function.
-- Examples:
--   applyAt 0 (x ↦ y ↦ ... ↦ f(x,y)) a = (y ↦ ... ↦ f(a,y))
--   applyAt 1 (x ↦ y ↦ ... ↦ f(x,y)) b = (x ↦ ... ↦ f(x,b))
--   applyAt 0 (x ↦ y ↦ z ↦ ... ↦ f(x,y,z)) a = (y ↦ z ↦ ... ↦ f(a,y,z))
--   applyAt 1 (x ↦ y ↦ z ↦ ... ↦ f(x,y,z)) b = (x ↦ z ↦ ... ↦ f(x,b,z))
--   applyAt 2 (x ↦ y ↦ z ↦ ... ↦ f(x,y,z)) c = (x ↦ y ↦ ... ↦ f(x,y,c))
applyAt : ∀{As : Types{𝐒(n)}(ℓ𝓈)}{B : Type{ℓ}} → (i : 𝕟(𝐒(n))) → (index i As) → (As ⇉ B) → (without i As ⇉ B)
applyAt {n = 0}       𝟎      xi f    = f xi
applyAt {n = 1}       𝟎      xi f x  = f xi x
applyAt {n = 1}       (𝐒(𝟎)) xi f x  = f x xi
applyAt {n = 𝐒(𝐒(n))} 𝟎      xi f xs = f xi xs
applyAt {n = 𝐒(𝐒(n))} (𝐒(i)) xi f x  = applyAt {n = 𝐒(n)} i xi (f(x))

_$[_]_ : ∀{As : Types{𝐒(n)}(ℓ𝓈)}{B : Type{ℓ}} → (As ⇉ B) → (i : 𝕟(𝐒(n))) → (index i As) → (without i As ⇉ B)
f $[ i ] x = applyAt i x f

-- Applies the same arguments `xₙ` on every inner function `gₙ`, and then apply these as the arguments to an outer function `f`.
-- This is similiar to (_on_) but uses different functions for every argument and every argument is applied to each function.
-- Example:
--   (onMany(n) f g₁ g₂ g₃ ...) x₁ x₂ x₃ ... = f (g₁ x₁) (g₂ x₂) (g₃ x₃) ...
-- TODO: Try to get rid of the curry/uncurry by using (_∘ᵣ_)
onMany : (n : ℕ) → ∀{ℓ𝓈₁}{As : Types{n}(ℓ𝓈₁)}{ℓ𝓈₂}{Bs : Types{n}(ℓ𝓈₂)}{C : Type{ℓ}} → (Bs ⇉ C) → (As ⦗ map₂(_→ᶠ_) ⦘ Bs) ⇉ (As ⇉ C)
onMany 𝟎             = id
onMany (𝐒(𝟎))        = _∘_
onMany (𝐒(𝐒(n))) f g = curry{n = n} (gs ↦ x ↦ apply{n = n} gs (onMany (𝐒(n)) (f(g(x)))))

{-module _ where
  postulate l1 l2 l3 l4 l5 l6 l7 l8 : Lvl.Level
  postulate A : Type{l1}
  postulate B : Type{l2}
  postulate C : Type{l3}
  postulate D : Type{l4}
  postulate E : Type{l5}
  postulate F : Type{l6}
  postulate G : Type{l7}
  postulate H : Type{l8}
  postulate fn : A → B → C → D
  postulate g1 : E → A
  postulate g2 : F → B
  postulate g3 : G → C
  postulate e : E
  postulate f : F
  postulate g : G
  test : D
  test = onMany(3) fn g1 g2 g3 e f g
-}

{-
-- Example:
--   (f ∘ₗ g₁ g₂ g₃ ...) x₁ x₂ x₃ ... = f (g₁ x₁ x₂ x₃ ...) (g₂ x₁ x₂ x₃ ...) (g₃ x₁ x₂ x₃ ...) ...
_∘ₗ : ∀{As : Types{n}(ℓ𝓈₁)}{Bs : Types{n}(ℓ𝓈₂)}{C : Type{ℓ}} → (Bs ⇉ C) → (map (As ⇉_) Bs) ⇉ (As ⇉ C)
_∘ₗ {n = 𝟎} = id
_∘ₗ {n = 𝐒 𝟎} = _∘_
_∘ₗ {n = 𝐒 (𝐒 n)} f g = curry{n = n} (gs ↦ x ↦ apply {n = n} gs {!_∘ₗ {n = 𝐒 n} ((f ∘ (g(x) $_)) ?)!})
-- _∘ₗ {n = 𝐒 n} (f ∘ g(x)) $_)
-- curry{n = n} (gs ↦ x ↦ curry{n = n} (xs ↦ ((_∘ₗ {n = 𝐒(n)} (f(g(x) $ xs)) $ Raise.map{n = 𝐒(𝐒(n))} (g ↦ g(x) $ xs) {!gs!}) $ xs)))
-- curry{n = n} (gs ↦ x ↦ curry{n = n} (xs ↦ {!f(g(x) $ xs) $ map(g ↦ g(x) $ xs) gs!}))
-}

-- TODO: Also a specialised (liftOn)? This is probably one of the parts of being an "applicative functor". The other being `const`
_$lifted_ : ∀{As : Types{n}(ℓ𝓈)}{B : Type{ℓ₁}}{C : Type{ℓ₂}} → (As ⇉ (B → C)) → ((As ⇉ B) → (As ⇉ C))
_$lifted_ {n = 𝟎}             = id
_$lifted_ {n = 𝐒(𝟎)}    f g x = f x (g x)
_$lifted_ {n = 𝐒(𝐒(n))} f g x = _$lifted_ {n = 𝐒 n} (f(x)) (g(x))

_,lifted_ : ∀{As : Types{n}(ℓ𝓈)}{B : Type{ℓ₁}}{C : Type{ℓ₂}} → (As ⇉ B) → (As ⇉ C) → (As ⇉ (B ⨯ C))
_,lifted_ {n = n} f g = _$lifted_ {n = n} ((swap₁ _,_) ∘ᵣ g) f

applyDuplicate : ∀{As : Types{n}(ℓ𝓈)}{B : Type{ℓ}} → (As ⇉ As ⇉ B) → (As ⇉ B)
applyDuplicate {n = 𝟎}            = id
applyDuplicate {n = 𝐒 𝟎}     f(x) = f(x)(x)
applyDuplicate {n = 𝐒 (𝐒 n)} f(x) = applyDuplicate {n = 𝐒 n} ((_$₁ x) ∘ᵣ (f(x)))

swap : ∀{As : Types{𝐒(n₁)}(ℓ𝓈₁)}{Bs : Types{𝐒(n₂)}(ℓ𝓈₂)}{C : Type{ℓ}} → (As ⇉ Bs ⇉ C) → (Bs ⇉ As ⇉ C)
swap {n₁ = n₁} {n₂ = 𝟎}    f b = (_$₁ b) ∘ᵣ f
swap {n₁ = n₁} {n₂ = 𝐒 n₂} f b = swap {n₁ = n₁} {n₂ = n₂} ((_$₁ b) ∘ᵣ f)

-- Puts the second function on every argument of the first function.
-- Example:
--   (f on g) x₁ x₂ x₃ .. = f (g x₁) (g x₂) (g x₃) ..
_on_ : ∀{A : Type{ℓ₁}}{B : Type{ℓ₂}}{C : Type{ℓ₃}} → (repeat n B ⇉ C) → (A → B) → (repeat n A ⇉ C)
_on_ {n = 𝟎}       f _       = f
_on_ {n = 𝐒(𝟎)}    f g x     = f(g(x))
_on_ {n = 𝐒(𝐒(n))} f g x     = _on_ {n = 𝐒(n)} (f(g(x))) g


-- TODO: How to implement something like this
--(F(x) ▫ F(y)) ▫ F(x . y) 
--_aryᵣFromBinaryOperator_ : (n : ℕ) → ∀{X : Type{ℓ₁}}{Y : Type{ℓ₂}} → (_▫_ : X → Y → X) → 
-- _aryᵣFromBinaryOperator_ : (n : ℕ) → ∀{F}{_○_} → (_▫_ : ∀{x y} → F(x) → F(y) → F(x ○ y)) → 

-- Nested quantifiers over multiple values.
-- Example:
--   quantifier₊(3) □(P) = □(x ↦ □(y ↦ □(z ↦ P(x)(y)(z))))
quantifier₊ : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (∀{ℓ₁ ℓ₂}{T : Type{ℓ₁}} → (T → Stmt{ℓ₂}) → Stmt{ℓ₁ Lvl.⊔ ℓ₂}) → (As ⇉ Stmt{ℓ}) → Stmt{ℓ Lvl.⊔ (Lvl.⨆(ℓ𝓈))}
quantifier₊ 0         □(P) = P
quantifier₊ 1         □(P) = □(P)
quantifier₊ (𝐒(𝐒(n))) □(P) = □(x ↦ quantifier₊(𝐒(n)) □(P(x)))

-- TODO: Move these
module _ where
  open import Logic.Predicate

  ∀₊ : (n : ℕ) → ∀{ℓ}{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (As ⇉ Stmt{ℓ}) → Stmt
  ∀₊(n) = quantifier₊(n) ∀ₗ

  ∃₊ : (n : ℕ) → ∀{ℓ}{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (As ⇉ Stmt{ℓ}) → Stmt
  ∃₊(n) = quantifier₊(n) ∃
