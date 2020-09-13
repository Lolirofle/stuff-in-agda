module Function.Multi.Functions where

open import Data
import      Data.Option.Functions as Option
open import Data.Tuple renaming (curry to curry₁ ; uncurry to uncurry₁) using (_⨯_ ; _,_)
open import Data.Tuple.Raise
import      Data.Tuple.Raiseᵣ.Functions as Raise
open import Data.Tuple.RaiseTypeᵣ
open import Data.Tuple.RaiseTypeᵣ.Functions
open import Function.Multi
open import Functional using (_→ᶠ_ ; id ; _∘_ ; _∘ᵢₙₛₜ_ ; _⦗_⦘_) renaming (const to const₁ ; apply to apply₁ ; swap to swap₁ ; _$_ to _$₁_)
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
private variable ℓ𝓈 ℓ𝓈₁ ℓ𝓈₂ : Lvl.Level ^ n
private variable A B C : Type{ℓ}
private variable As Bs Cs : Types{n}(ℓ𝓈)

-- TODO: Make all n, n₁, n₂ explicit. Find a way to do this while having generalized variables

-- A constant function of many variables.
-- Lifts a value to being a number of nested functions.
-- Examples:
--   const(x) _ _ _ ... = x
--   const(x)
--   = (const₁ ∘ const₁ ∘ const₁ ∘ ...)(x)
--   = (_ ↦ (_ ↦ (_ ↦ x)))
--   = (_ ↦ _ ↦ _ ↦ x)
const : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)}{ℓ}{B : Type{ℓ}} → B → (As ⇉ B)
const(0)       = id
const(1)       = const₁
const(𝐒(𝐒(n))) = const₁ ∘ const(𝐒(n))

-- A projection function of many variables.
-- Returns one of the specified arguments.
-- Examples:
--   proj(2)(0) x y = x
--   proj(2)(1) x y = y
--   proj(3)(0) x y z = x
--   proj(3)(1) x y z = y
--   proj(3)(2) x y z = z
--   proj(4)(0) x y z w = x
--   proj(4)(1) x y z w = y
--   proj(4)(2) x y z w = z
--   proj(4)(3) x y z w = w
proj : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (i : 𝕟(n)) → (As ⇉ index i As)
proj(1)       𝟎      x = x
proj(𝐒(𝐒(n))) 𝟎      x = const(𝐒(n)) x
proj(𝐒(𝐒(n))) (𝐒(i)) _ = proj(𝐒(n)) i

-- Applies a function on the return value of a multivariate function.
-- Composes the first argument and the last function of the second argument.
-- Can also be seen as lifting the function type to the structure of (As ⇉_).
-- Examples:
--   f ∘ᵣ g = (((f ∘_) ∘_) ∘_) ..
--   ((((f ∘ᵣ g) x₁) x₂) x₃) .. = f((((g x₁) x₂) x₃) ..)
--   (f ∘ᵣ g) x₁ x₂ x₃ .. = f(g x₁ x₂ x₃ ..)
-- Note: This can be used to specify the `map` function of a functor (As ⇉_).
compose : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)}{ℓ₁}{B : Type{ℓ₁}}{ℓ₂}{C : Type{ℓ₂}} → (B → C) → (As ⇉ B) → (As ⇉ C)
compose(0)         = id
compose(1)         = _∘_
compose(𝐒(𝐒(n))) f = compose(𝐒(n)) f ∘_
_∘ᵣ_ : ∀{As : Types{n}(ℓ𝓈)}{B : Type{ℓ₁}}{C : Type{ℓ₂}} → (B → C) → (As ⇉ B) → (As ⇉ C)
_∘ᵣ_ {n = n} = compose(n)

composeᵢₙₛₜ : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)}{ℓ₁}{B : Type{ℓ₁}}{ℓ₂}{C : Type{ℓ₂}} → (B → C) → (As ⇉ᵢₙₛₜ B) → (As ⇉ᵢₙₛₜ C)
composeᵢₙₛₜ(0)           = id
composeᵢₙₛₜ(1)       f g = f(g)
composeᵢₙₛₜ(𝐒(𝐒(n))) f g = composeᵢₙₛₜ(𝐒(n)) f g

-- Puts the second function on every argument of the first function.
-- Example:
--   (f on g) x₁ x₂ x₃ .. = f (g x₁) (g x₂) (g x₃) ..
composeOnEvery : (n : ℕ) → ∀{ℓ₁}{A : Type{ℓ₁}}{ℓ₂}{B : Type{ℓ₂}}{ℓ₃}{C : Type{ℓ₃}} → (repeat n B ⇉ C) → (A → B) → (repeat n A ⇉ C)
composeOnEvery 0               = const₁
composeOnEvery 1               = _∘_
composeOnEvery (𝐒(𝐒(n))) f g x = composeOnEvery(𝐒(n)) (f(g(x))) g
_on_ : ∀{A : Type{ℓ₁}}{B : Type{ℓ₂}}{C : Type{ℓ₃}} → (repeat n B ⇉ C) → (A → B) → (repeat n A ⇉ C)
_on_ {n = n} = composeOnEvery(n)

applyTwice : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)}{ℓ}{B : Type{ℓ}} → (As ⇉ As ⇉ B) → (As ⇉ B)
applyTwice(0)            = id
applyTwice(1)       f(x) = f(x)(x)
applyTwice(𝐒(𝐒(n))) f(x) = applyTwice(𝐒(n)) ((_$₁ x) ∘ᵣ (f(x)))

swap : (n₁ n₂ : ℕ) → ∀{ℓ𝓈₁}{As : Types{n₁}(ℓ𝓈₁)}{ℓ𝓈₂}{Bs : Types{n₂}(ℓ𝓈₂)}{ℓ}{C : Type{ℓ}} → (As ⇉ Bs ⇉ C) → (Bs ⇉ As ⇉ C)
swap(n₁)(0)            = id
swap(n₁)(1)        f b = (_$₁ b) ∘ᵣ f
swap(n₁)(𝐒(𝐒(n₂))) f b = swap(n₁)(𝐒(n₂)) ((_$₁ b) ∘ᵣ f)

-- Lifts a function/operator pointwise.
-- A generalized variant of `(_∘ᵣ_)` that allows the left function to have multiple arguments.
-- Example:
--   (f ∘ₗ g₁ g₂ g₃ ...) x₁ x₂ x₃ ... = f (g₁ x₁ x₂ x₃ ...) (g₂ x₁ x₂ x₃ ...) (g₃ x₁ x₂ x₃ ...) ...
--   (f ∘ₗ g) x₁ x₂ x₃ ... = (f ∘ᵣ g) x₁ x₂ x₃ ...
--   pointwise(1)(2) (_+_) = (f ↦ g ↦ x ↦ f(x) + g(x))
pointwise : (n₁ n₂ : ℕ) → ∀{ℓ𝓈₁}{As : Types{n₁}(ℓ𝓈₁)}{ℓ𝓈₂}{Bs : Types{n₂}(ℓ𝓈₂)}{ℓ}{C : Type{ℓ}} → (Bs ⇉ C) → (map (As ⇉_) Bs) ⇉ (As ⇉ C)
pointwise(n₁)(0)            = const(n₁)
pointwise(n₁)(1)            = compose(n₁)
pointwise(n₁)(𝐒(𝐒(n₂))) {As = As}{Bs = B , Bs}{C = C} f g = p{n = 𝐒(n₂)} (pointwise(n₁)(𝐒(n₂))) (f ∘ᵣ g) where
  p : ∀{Ts : Types{n}(ℓ𝓈)} → ((Bs ⇉ C) → (Ts ⇉ As ⇉ C)) → ((As ⇉ Bs ⇉ C) → (Ts ⇉ As ⇉ C)) -- TODO: Is it possible to simplify this helper function?
  p{n = n}{Ts = Ts} f g = compose(n) (applyTwice(n₁)) (swap(n₁)(n) (compose(n₁) f g))
_∘ₗ : ∀{As : Types{n₁}(ℓ𝓈₁)}{Bs : Types{n₂}(ℓ𝓈₂)}{C : Type{ℓ}} → (Bs ⇉ C) → (map (As ⇉_) Bs) ⇉ (As ⇉ C)
_∘ₗ {n₁ = n₁}{n₂ = n₂} = pointwise(n₁)(n₂)

-- Converts a function using a tuple to represent its arguments to a curried function (nested function types).
-- Example:
--   curry((x,y,z,...) ↦ φ) = (x ↦ y ↦ z ↦ ... ↦ φ)
--   curry(0) = id                       : (A₁                  → B) → (A₁                → B)
--   curry(1) = curry₁                   : ((A₁ ⨯ A₂)           → B) → (A₁ → A₂           → B)
--   curry(2) = curry₁ ∘ curry₁          : ((A₁ ⨯ A₂ ⨯ A₃)      → B) → (A₁ → A₂ → A₃      → B)
--   curry(3) = curry₁ ∘ curry₁ ∘ curry₁ : ((A₁ ⨯ A₂ ⨯ A₃ ⨯ A₄) → B) → (A₁ → A₂ → A₃ → A₄ → B)
-- Note: If there is a nested uncurry and curry, one can often rewrite it using (_∘ᵣ_) instead (I think).
curry : (n : ℕ) → ∀{ℓ𝓈}{As : Types{𝐒(n)}(ℓ𝓈)}{ℓ}{B : Type{ℓ}} → (reduceᵣ(_⨯_) As → B) → (As ⇉ B)
curry(𝟎)        = id
curry(𝐒(n)) f x = curry(n) (f ∘ (x ,_))

-- Converts a curried function (nested function types) to a function using a tuple to represent its arguments.
-- Example:
--   uncurry(x ↦ y ↦ z ↦ ... ↦ φ) = ((x,y,z,...) ↦ φ)
uncurry : (n : ℕ) → ∀{ℓ𝓈}{As : Types{𝐒(n)}(ℓ𝓈)}{ℓ}{B : Type{ℓ}} → (As ⇉ B) → (reduceᵣ(_⨯_) As → B)
uncurry(𝟎)               = id
uncurry(𝐒(n)) f (x , xs) = uncurry(n) (f(x)) xs

-- Applies a tuple as arguments to a multivariate function.
-- Example:
--   apply(x,y,z,...) (x ↦ y ↦ z ↦ ... ↦ φ) = φ
applyTuple : (n : ℕ) → ∀{ℓ𝓈}{As : Types{𝐒(n)}(ℓ𝓈)}{ℓ}{B : Type{ℓ}} → (reduceᵣ(_⨯_) As) → (As ⇉ B) → B
applyTuple(n) = swap₁(uncurry(n))

-- Applies an argument to a specific position in the arguments of an argument list of a multivariate function.
-- Examples:
--   applyAt 0 (x ↦ y ↦ ... ↦ f(x,y)) a = (y ↦ ... ↦ f(a,y))
--   applyAt 1 (x ↦ y ↦ ... ↦ f(x,y)) b = (x ↦ ... ↦ f(x,b))
--   applyAt 0 (x ↦ y ↦ z ↦ ... ↦ f(x,y,z)) a = (y ↦ z ↦ ... ↦ f(a,y,z))
--   applyAt 1 (x ↦ y ↦ z ↦ ... ↦ f(x,y,z)) b = (x ↦ z ↦ ... ↦ f(x,b,z))
--   applyAt 2 (x ↦ y ↦ z ↦ ... ↦ f(x,y,z)) c = (x ↦ y ↦ ... ↦ f(x,y,c))
applyAt : (n : ℕ) → ∀{ℓ𝓈}{As : Types{𝐒(n)}(ℓ𝓈)}{ℓ}{B : Type{ℓ}} → (i : 𝕟(𝐒(n))) → (index i As) → (As ⇉ B) → (without i As ⇉ B)
applyAt(0)       𝟎      xi f    = f xi
applyAt(1)       𝟎      xi f x  = f xi x
applyAt(1)       (𝐒(𝟎)) xi f x  = f x xi
applyAt(𝐒(𝐒(n))) 𝟎      xi f xs = f xi xs
applyAt(𝐒(𝐒(n))) (𝐒(i)) xi f x  = applyAt(𝐒(n)) i xi (f(x))

-- Puts the second and each succeeding functions on the respective arguments of the first function.
-- Applies each argument `xₙ` on the inner function `gₙ`, and then apply the value of these as the arguments to an outer function `f`.
-- This is similiar to (_on_) but uses different functions for every argument and each argument is applied to its respective function instead.
-- Example:
--   (onMany(n) f g₁ g₂ g₃ ...) x₁ x₂ x₃ ... = f (g₁ x₁) (g₂ x₂) (g₃ x₃) ...
-- TODO: Try to get rid of the curry/uncurry by using (_∘ᵣ_)
onEach : (n : ℕ) → ∀{ℓ𝓈₁}{As : Types{n}(ℓ𝓈₁)}{ℓ𝓈₂}{Bs : Types{n}(ℓ𝓈₂)}{C : Type{ℓ}} → (Bs ⇉ C) → (As ⦗ map₂(_→ᶠ_) ⦘ Bs) ⇉ (As ⇉ C)
onEach(0)           = id
onEach(1)           = _∘_
onEach(𝐒(𝐒(n))) f g = curry(n) (gs ↦ x ↦ uncurry(n) (onEach(𝐒(n)) (f(g(x)))) gs)

-- Note: One of the parts of being an "applicative functor". The other being `const`
liftedApply : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)}{ℓ₁}{B : Type{ℓ₁}}{ℓ₂}{C : Type{ℓ₂}} → (As ⇉ (B → C)) → ((As ⇉ B) → (As ⇉ C))
liftedApply(0)             = id
liftedApply(1)       f g x = f x (g x)
liftedApply(𝐒(𝐒(n))) f g x = liftedApply(𝐒(n)) (f(x)) (g(x))

lifted-[,] : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)}{ℓ₁}{B : Type{ℓ₁}}{ℓ₂}{C : Type{ℓ₂}} → (As ⇉ B) → (As ⇉ C) → (As ⇉ (B ⨯ C))
lifted-[,](n) f g = liftedApply(n) ((swap₁ _,_) ∘ᵣ g) f

-- TODO: How to implement something like this
--(F(x) ▫ F(y)) ▫ F(x . y) 
--_aryᵣFromBinaryOperator_ : (n : ℕ) → ∀{X : Type{ℓ₁}}{Y : Type{ℓ₂}} → (_▫_ : X → Y → X) → 
-- _aryᵣFromBinaryOperator_ : (n : ℕ) → ∀{F}{_○_} → (_▫_ : ∀{x y} → F(x) → F(y) → F(x ○ y)) →
-- _aryᵣFromBinaryOperator_ : (n : ℕ) → ∀{F} → (_▫_ : ∀{x y z} → F(x)(y) → F(y)(z) → F(x)(z)) →
-- CategoricalOperator₊ : ℕ → {Obj : Type{ℓ₁}} → (Obj → Obj → Type{ℓ₂}) → Type
-- CategoricalOperator₊(0)       F = ∀{x₁ x₂} → F(x₁)(x₂) → F(x₁)(x₂)
-- CategoricalOperator₊(1)       F = ∀{x₁ x₂ x₃} → F(x₂)(x₃) → F(x₁)(x₂) → F(x₁)(x₃)
-- CategoricalOperator₊(𝐒(𝐒(n))) F = {!!}

-- Nested quantifiers over multiple values.
-- Used to defined 
-- Example:
--   quantifier₊(3) □(P) = □(x ↦ □(y ↦ □(z ↦ P(x)(y)(z))))
quantifier₊ : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (∀{ℓ₁ ℓ₂}{T : Type{ℓ₁}} → (T → Stmt{ℓ₂}) → Stmt{ℓ₁ Lvl.⊔ ℓ₂}) → (As ⇉ Stmt{ℓ}) → Stmt{ℓ Lvl.⊔ (Lvl.⨆(ℓ𝓈))}
quantifier₊(0)       □(P) = P
quantifier₊(1)       □(P) = □(P)
quantifier₊(𝐒(𝐒(n))) □(P) = □(x ↦ quantifier₊(𝐒(n)) □(P(x)))

quantifier₊ᵢₘₚₗ : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (∀{ℓ₁ ℓ₂}{T : Type{ℓ₁}} → (T → Stmt{ℓ₂}) → Stmt{ℓ₁ Lvl.⊔ ℓ₂}) → (As ⇉ᵢₘₚₗ Stmt{ℓ}) → Stmt{ℓ Lvl.⊔ (Lvl.⨆(ℓ𝓈))}
quantifier₊ᵢₘₚₗ(0)       □(P) = P
quantifier₊ᵢₘₚₗ(1)       □(P) = □(x ↦ P{x})
quantifier₊ᵢₘₚₗ(𝐒(𝐒(n))) □(P) = □(x ↦ quantifier₊ᵢₘₚₗ(𝐒(n)) □(P{x}))

quantifier₊ᵢₙₛₜ : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (∀{ℓ₁ ℓ₂}{T : Type{ℓ₁}} → (T → Stmt{ℓ₂}) → Stmt{ℓ₁ Lvl.⊔ ℓ₂}) → (As ⇉ᵢₙₛₜ Stmt{ℓ}) → Stmt{ℓ Lvl.⊔ (Lvl.⨆(ℓ𝓈))}
quantifier₊ᵢₙₛₜ(0)       □(P) = P
quantifier₊ᵢₙₛₜ(1)       □(P) = □(x ↦ P ⦃ x ⦄)
quantifier₊ᵢₙₛₜ(𝐒(𝐒(n))) □(P) = □(x ↦ quantifier₊ᵢₙₛₜ(𝐒(n)) □(P ⦃ x ⦄))

quantify : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (As ⇉ Stmt{ℓ}) → Stmt{ℓ Lvl.⊔ (Lvl.⨆(ℓ𝓈))}
quantify(n) P = quantifier₊(n) (Pred ↦ (∀(x) → Pred(x))) P

quantifyᵢₘₚₗ : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (As ⇉ᵢₘₚₗ Stmt{ℓ}) → Stmt{ℓ Lvl.⊔ (Lvl.⨆(ℓ𝓈))}
quantifyᵢₘₚₗ(n) P = quantifier₊ᵢₘₚₗ(n) (Pred ↦ (∀{x} → Pred(x))) P

quantifyᵢₙₛₜ : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (As ⇉ᵢₙₛₜ Stmt{ℓ}) → Stmt{ℓ Lvl.⊔ (Lvl.⨆(ℓ𝓈))}
quantifyᵢₙₛₜ(n) P = quantifier₊ᵢₙₛₜ(n) (Pred ↦ (∀ ⦃ x ⦄ → Pred(x))) P

quantifierSpecific : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (∀{i} → (index i As → Stmt{ℓ}) → Stmt{ℓ}) → (As ⇉ Stmt{ℓ}) → Stmt{ℓ}
quantifierSpecific(0)       □(P) = P
quantifierSpecific(1)       □(P) = □{𝟎}(P)
quantifierSpecific(𝐒(𝐒(n))) □(P) = □{𝟎}(x ↦ quantifierSpecific(𝐒(n)) (\{i} → □{𝐒(i)})(P(x)))

{- TODO: MOre general levels
quantifierSpecific : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (∀{i} → (index i As → Stmt{Raise.index i ℓ𝓈}) → Stmt{ℓ}) → (As ⇉ Stmt{Lvl.⨆(ℓ𝓈)}) → Stmt{(Raise.head₀ ℓ𝓈) Option.or ℓ}
quantifierSpecific(0)       □(P) = {!!}
quantifierSpecific(1)       □(P) = □{𝟎}(P)
quantifierSpecific(𝐒(𝐒(n))) □(P) = □{𝟎}(x ↦ {!quantifierSpecific(𝐒(n)) (\{i} → □{𝐒(i)})(P(x))!})
-}

expl-to-impl : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)}{ℓ}{B : Type{ℓ}} → (As ⇉ B) → (As ⇉ᵢₘₚₗ B)
expl-to-impl 0         f = f
expl-to-impl 1         f{x} = f(x)
expl-to-impl (𝐒(𝐒(n))) f{x} = expl-to-impl(𝐒(n)) (f(x))

expl-to-inst : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)}{ℓ}{B : Type{ℓ}} → (As ⇉ B) → (As ⇉ᵢₙₛₜ B)
expl-to-inst 0         f = f
expl-to-inst 1         f ⦃ x ⦄ = f(x)
expl-to-inst (𝐒(𝐒(n))) f ⦃ x ⦄ = expl-to-inst(𝐒(n)) (f(x))

impl-to-expl : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)}{ℓ}{B : Type{ℓ}} → (As ⇉ᵢₘₚₗ B) → (As ⇉ B)
impl-to-expl 0         f = f
impl-to-expl 1         f(x) = f{x}
impl-to-expl (𝐒(𝐒(n))) f(x) = impl-to-expl(𝐒(n)) (f{x})

inst-to-expl : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)}{ℓ}{B : Type{ℓ}} → (As ⇉ᵢₙₛₜ B) → (As ⇉ B)
inst-to-expl 0         f = f
inst-to-expl 1         f(x) = f ⦃ x ⦄
inst-to-expl (𝐒(𝐒(n))) f(x) = inst-to-expl(𝐒(n)) (f ⦃ x ⦄)
