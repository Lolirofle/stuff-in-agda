module Function.Multi where

open import Data
open import Data.Tuple renaming (curry to curry₁ ; uncurry to uncurry₁) hiding (swap ; map)
open import Data.Tuple.Raiseᵣ
open import Functional using (_→ᶠ_ ; id ; _∘_ ; _〔_〕_) renaming (const to const₁ ; apply to apply₁ ; swap to swap₁ ; _$_ to _$₁_)
import      Lvl
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Natural
open import Syntax.Function
open import Syntax.Number
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ : Lvl.Level

infixr 0 _⇉_
infixr 2 _$_

-- Construction of a multivariate function type (nested by repeated application of (_→_)) of different types from a tuple list of types.
-- Example:
--   ((A,B,C,D,..) ⇉ R)
--   = (A → (B → (C → (D → (.. → R)))))
--   = (A → B → C → D → .. → R)
-- Note:
--   This can be defined as:
--   `(As ⇉ B) = foldᵣ(_→ᶠ_) B As`
--   but it is not because apparently inference takes a hit.
-- TODO: Generalize. This is a relation for nested (_⟶_). One can also define a relation for nested (_⇉_). Currying would be different, but it is essentially the same thing. See for example the implementation of (_∘ₗ_) where 
_⇉_ : ∀{n : ℕ} → (Type{ℓ} ^ n) → Type{ℓ} → Type{ℓ}
_⇉_ {n = 𝟎}       _        B = B
_⇉_ {n = 𝐒(𝟎)}    A        B = A → B
_⇉_ {n = 𝐒(𝐒(n))} (A , As) B = A → (As ⇉ B)

-- A constant function of many variables.
-- Lifts a value to being a number of nested functions.
-- Examples:
--   const(x) _ _ _ ... = x
--   const(x)
--   = (const₁ ∘ const₁ ∘ const₁ ∘ ...)(x)
--   = (_ ↦ (_ ↦ (_ ↦ x)))
--   = (_ ↦ _ ↦ _ ↦ x)
const : ∀{n}{As : Type{ℓ} ^ n}{B} → B → (As ⇉ B)
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
proj : ∀{n}{As : Type{ℓ} ^ n} → (i : 𝕟(n)) → (As ⇉ index i As)
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
_∘ᵣ_ : ∀{n}{As : Type{ℓ} ^ n}{B C} → (B → C) → (As ⇉ B) → (As ⇉ C)
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

curry : ∀{n}{As : Type{ℓ} ^ 𝐒(n)}{B} → (reduceᵣ(_⨯_) As → B) → (As ⇉ B)
curry {n = 𝟎}        = id
curry {n = 𝐒(n)} f x = curry {n = n} (f ∘ (x ,_))

curry₀ : ∀{n}{As : Type{ℓ} ^ n}{B} → (mapReduceᵣ(_⨯_) B (_→ᶠ B) As) → (As ⇉ B)
curry₀ {n = 𝟎}    = id
curry₀ {n = 𝐒(n)} = curry {n = n}

-- Converts a curried function (nested function types) to a function using a tuple to represent its arguments.
-- Example:
--   uncurry(x ↦ y ↦ z ↦ ... ↦ φ) = ((x,y,z,...) ↦ φ)
uncurry : ∀{n}{As : Type{ℓ} ^ 𝐒(n)}{B} → (As ⇉ B) → (reduceᵣ(_⨯_) As → B)
uncurry {n = 𝟎}               = id
uncurry {n = 𝐒(n)} f (x , xs) = uncurry {n = n} (f(x)) xs

uncurry₀ : ∀{n}{As : Type{ℓ} ^ n}{B} → (As ⇉ B) → (mapReduceᵣ(_⨯_) B (_→ᶠ B) As)
uncurry₀ {n = 𝟎}    = id
uncurry₀ {n = 𝐒(n)} = uncurry {n = n}

-- Applies a tuple as arguments to a multivariate function.
-- Example:
--   apply(x,y,z,...) (x ↦ y ↦ z ↦ ... ↦ φ) = φ
apply : ∀{n}{As : Type{ℓ} ^ 𝐒(n)}{B} → (reduceᵣ(_⨯_) As) → (As ⇉ B) → B
apply = swap₁ uncurry

_$_ = uncurry

-- Applies an argument to a specific position in the arguments of an argument list of a multivariate function.
-- Examples:
--   applyAt 0 (x ↦ y ↦ ... ↦ f(x,y)) a = (y ↦ ... ↦ f(a,y))
--   applyAt 1 (x ↦ y ↦ ... ↦ f(x,y)) b = (x ↦ ... ↦ f(x,b))
--   applyAt 0 (x ↦ y ↦ z ↦ ... ↦ f(x,y,z)) a = (y ↦ z ↦ ... ↦ f(a,y,z))
--   applyAt 1 (x ↦ y ↦ z ↦ ... ↦ f(x,y,z)) b = (x ↦ z ↦ ... ↦ f(x,b,z))
--   applyAt 2 (x ↦ y ↦ z ↦ ... ↦ f(x,y,z)) c = (x ↦ y ↦ ... ↦ f(x,y,c))
applyAt : ∀{n}{As : Type{ℓ} ^ 𝐒(n)}{B} → (i : 𝕟(𝐒(n))) → (index i As) → (As ⇉ B) → (without i As ⇉ B)
applyAt {n = 0}       𝟎      xi f    = f xi
applyAt {n = 1}       𝟎      xi f x  = f xi x
applyAt {n = 1}       (𝐒(𝟎)) xi f x  = f x xi
applyAt {n = 𝐒(𝐒(n))} 𝟎      xi f xs = f xi xs
applyAt {n = 𝐒(𝐒(n))} (𝐒(i)) xi f x  = applyAt {n = 𝐒(n)} i xi (f(x))

_$[_]_ : ∀{n}{As : Type{ℓ} ^ 𝐒(n)}{B} → (As ⇉ B) → (i : 𝕟(𝐒(n))) → (index i As) → (without i As ⇉ B)
f $[ i ] x = applyAt i x f

-- Applies the same arguments `xₙ` on every inner function `gₙ`, and then apply these as the arguments to an outer function `f`.
-- This is similiar to (_on_) but uses different functions for every argument and every argument is applied to each function.
-- Example:
--   (f ∘ₗ g₁ g₂ g₃ ...) x₁ x₂ x₃ ... = f (g₁ x₁) (g₂ x₂) (g₃ x₃) ...
-- TODO: Try to get rid of the curry/uncurry by using (_∘ᵣ_)
_∘ₗ : ∀{n}{As : Type{ℓ} ^ n}{Bs : Type{ℓ} ^ n}{C} → (Bs ⇉ C) → (As 〔 map₂(_→ᶠ_) 〕 Bs) ⇉ (As ⇉ C)
_∘ₗ {n = 𝟎}      = id
_∘ₗ {n = 𝐒(𝟎)}   = _∘_
_∘ₗ {n = 𝐒(𝐒(n))} f g = curry{n = n} (gs ↦ x ↦ apply{n = n} gs (_∘ₗ {n = 𝐒(n)} (f(g(x)))))
-- _∘ᵣ_ {n = 𝐒 (𝐒 n)} {As 〔 map₂ _→ᶠ_ 〕 Bs} {_} {As ⇉ C} (((λ g x → _∘ᵣ_ {n = 𝐒 (𝐒 n)} {right As} {_} {C})) {!!}) (\g → {!!})
-- _∘ᵣ_ {n = 𝐒 (𝐒 n)} {As 〔 map₂(_→ᶠ_) 〕 Bs} {_} {As ⇉ C} (_∘ᵣ_ {n = 𝐒 (𝐒 n)} {!f!}) (g ↦ _∘ᵣ_ {n = 𝐒 (𝐒 n)} {!!} ([↦] (x ↦ _∘ₗ {n = 𝐒(n)} {right As} {right Bs} (f(g(x))))) {!!})
-- {!_∘ᵣ_ {n = 𝐒(𝐒(n))} {As} {_} {As ⇉ C} (x ↦ (_∘ₗ {n = 𝐒(n)} (f(g(x))))) ? ?!}
-- _∘ₗ {n = 𝐒(n)} f = curry{n = n} (gs ↦ curry{n = n} (xs ↦ f $ (fnsToMultivariate{n = n} gs) $ xs))
-- _∘ₗ {n = 𝐒(𝐒(n))} f g = curry{n = n} (gs ↦ x ↦ apply{n = n} gs (_∘ₗ {n = 𝐒(n)} (f(g(x)))))

-- Example:
--   (f ∘ₗ g₁ g₂ g₃ ...) x₁ x₂ x₃ ... = f (g₁ x₁ x₂ x₃ ...) (g₂ x₁ x₂ x₃ ...) (g₃ x₁ x₂ x₃ ...) ...

-- TODO: Also a specialised (liftOn)? This is probably one of the parts of being an "applicative functor". The other being `const`
_$lifted_ : ∀{n}{As : Type{ℓ} ^ n}{B C} → (As ⇉ (B → C)) → ((As ⇉ B) → (As ⇉ C))
_$lifted_ {n = 𝟎}             = id
_$lifted_ {n = 𝐒(𝟎)}    f g x = f x (g x)
_$lifted_ {n = 𝐒(𝐒(n))} f g x = _$lifted_ {n = 𝐒 n} (f(x)) (g(x))

_,lifted_ : ∀{n}{As : Type{ℓ} ^ n}{B C} → (As ⇉ B) → (As ⇉ C) → (As ⇉ (B ⨯ C))
_,lifted_ {n = n} f g = _$lifted_ {n = n} ((swap₁ _,_) ∘ᵣ g) f

applyDuplicate : ∀{n}{As : Type{ℓ} ^ n}{B} → (As ⇉ As ⇉ B) → (As ⇉ B)
applyDuplicate {n = 𝟎}            = id
applyDuplicate {n = 𝐒 𝟎}     f(x) = f(x)(x)
applyDuplicate {n = 𝐒 (𝐒 n)} f(x) = applyDuplicate {n = 𝐒 n} ((_$₁ x) ∘ᵣ (f(x)))

swap : ∀{n₁ n₂}{As : Type{ℓ} ^ 𝐒(n₁)}{Bs : Type{ℓ} ^ 𝐒(n₂)}{C} → (As ⇉ Bs ⇉ C) → (Bs ⇉ As ⇉ C)
swap {n₁ = n₁} {n₂ = 𝟎}    f b = (_$₁ b) ∘ᵣ f
swap {n₁ = n₁} {n₂ = 𝐒 n₂} f b = swap {n₁ = n₁} {n₂ = n₂} ((_$₁ b) ∘ᵣ f)

-- ? : ∀{n}{As : Type{ℓ} ^ 𝐒(n)}{B} → (As ⇉ B) → (without maximum As ⇉ (A → B))

-- Puts the second function on every argument of the first function.
-- Example:
--   (f on g) x₁ x₂ x₃ .. = f (g x₁) (g x₂) (g x₃) ..
_on_ : ∀{n}{A : Type{ℓ}}{B : Type{ℓ}}{C : Type{ℓ}} → (repeat n B ⇉ C) → (A → B) → (repeat n A ⇉ C)
_on_ {n = 𝟎}       f _       = f
_on_ {n = 𝐒(𝟎)}    f g x     = f(g(x))
_on_ {n = 𝐒(𝐒(n))} f g x     = _on_ {n = 𝐒(n)} (f(g(x))) g

-- Constructs a single function taking multiple arguments returning multiple values from a list of functions.
-- The resulting function is a function where each value is dependent on only one of its arguments.
-- Note: The converse is not possible in general because one value can depend on multiple arguments. See `splitMultivariate` for a possible implementation of this idea.
-- TODO: Why is this uncurried
fnsToMultivariate : ∀{n}{As Bs : Type{ℓ} ^ 𝐒(n)} → (reduceᵣ(_⨯_) (As 〔 map₂(_→ᶠ_) 〕 Bs)) → (As ⇉ reduceᵣ(_⨯_) Bs)
fnsToMultivariate {n = 𝟎}               = id
fnsToMultivariate {n = 𝐒(n)} (f , fs) x = (f(x) ,_) ∘ᵣ fnsToMultivariate{n = n} fs

{-
splitMultivariate : ∀{n}{As Bs : Type{ℓ} ^ 𝐒(n)} → (As ⇉ reduceᵣ(_⨯_) Bs) → (reduceᵣ(_⨯_) (map (As ⇉_) Bs))
splitMultivariate {n = 𝟎} f = f
left (splitMultivariate {n = 𝐒 n} f) x = left ∘ᵣ f x
right (splitMultivariate {n = 𝐒 n} f) = {!!}

joinMultivariate : ∀{n₁ n₂}{As : Type{ℓ} ^ 𝐒(n₁)}{Bs : Type{ℓ} ^ 𝐒(n₂)} → (reduceᵣ(_⨯_) (map (As ⇉_) Bs)) → (As ⇉ reduceᵣ(_⨯_) Bs)
joinMultivariate {n₁ = _}   {𝟎}    = id
joinMultivariate {n₁ = 𝟎} {𝐒 n₂} (f , fs) x = (f(x) , joinMultivariate {n₁ = 𝟎} {n₂} fs x)
joinMultivariate {n₁ = 𝐒 n₁} {𝐒 n₂} (f , fs) x = ((f x $ {!!}) ,_) ∘ᵣ joinMultivariate {n₁ = 𝐒(n₁)} {n₂} fs x
-- TODO: Needs the argument on LHS in _∘ᵣ_
-}

{-
right As ⇉ reduceᵣ _⨯_ (right Bs)
right As ⇉ left Bs ⨯ reduceᵣ _⨯_ (right Bs)

reduceᵣ _⨯_ (right Bs)
left Bs ⨯ reduceᵣ _⨯_ (right Bs)
-}

{-
-- TODO: Maps all the different As^n using the the (As ⇉ B) function.
mapn : ∀{n a}{As : Type{ℓ} ^ a}{B} → (As ⇉ B) → (map (_^ n) As ⇉ (B ^ n))
mapn {n = n}       {𝟎}       = repeat n
mapn {n = n}       {𝐒(𝟎)}    = map
mapn {n = 𝟎}       {𝐒(𝐒(a))} = const{n = {!!}} <>
mapn {n = 𝐒(𝟎)}    {𝐒(𝐒(a))} {As} = {!!} -- uncurry {n = a}--  {As = map (_^ 𝐒 𝟎) As}
mapn {n = 𝐒(𝐒(n))} {𝐒(𝐒(a))} = {!!}
-}

{-mapn {n = 𝟎}       f          = <>
mapn {n = 𝐒(𝟎)}    f x        = f(x)
mapn {n = 𝐒(𝐒(n))} f (x , xs) = {!!}
-- (f(x) , mapn {n = 𝐒(n)} f(xs))
-}

{-
-- TODO: Like _on_ but different functions instead of different arguments. Here, the arguments are the same on every "thing" instead.
liftOn : ∀{n₁ n₂}{As : Type{ℓ} ^ n₁}{Bs : Type{ℓ} ^ n₂}{C} → (Bs ⇉ C) → (map(As ⇉_) Bs ⇉ (As ⇉ C))
liftOn {n₁ = 𝐒(_)} {n₂ = 𝟎} = const
liftOn {n₁ = 𝐒(𝟎)} {n₂ = 𝐒(𝐒(𝟎))} _▫_ f g x = f(x) ▫ g(x)
liftOn {n₁ = 𝟎} {n₂ = 𝟎} = id
liftOn {n₁ = 𝟎} {n₂ = 𝐒 𝟎} = id
liftOn {n₁ = 𝟎} {n₂ = 𝐒 (𝐒 n₂)} x = {!!}
-- liftOn {n₁ = 𝐒(𝐒 n₁)} {n₂ = 𝐒(𝐒 n₂)} = liftOn{n₁ = 𝐒(𝐒(n₁))}{n₂ = 𝐒(n₂)} (_$_) ∘ᵣ liftOn{n₁ = 𝐒(𝐒(n₁))}{n₁ = 𝐒(n₂)}
-}

-- liftOn : ∀{n₁ n₂}{As : Type{ℓ} ^ n₁}{Bs : Type{ℓ} ^ n₂}{C} → (Bs ⇉ C) → (map(As ⇉_) Bs ⇉ (As ⇉ C))
{-liftOn {n₁ = 𝟎} {n₂ = n₂} = {!!}
liftOn {n₁ = 𝐒 𝟎} {n₂ = n₂} = {!!}
liftOn {n₁ = 𝐒(𝐒 n₁)} {n₂ = n₂} {A , As}{Bs}{C} f = {!!}
-- _∘_ (liftOn {n₁ = 𝐒(𝐒 n₁)}{n₂ = 𝐒(𝐒 n₂)} {A₂ , As}{Bs}{C}) (liftOn {n₁ = 𝐒 n₁} {n₂ = 𝐒(𝐒 n₂)} {As}{Bs}{C})
-}

-- liftOn {n₁ = n₁} {n₂ = 𝟎} = const
-- liftOn {n₁ = n₁} {n₂ = 𝐒 𝟎} = _∘ᵣ_
-- liftOn {n₁ = n₁} {n₂ = 𝐒(𝐒 n₂)} {As}{B , Bs}{C} f g = test{n = 𝐒 n₂} (f ∘ᵣ g) (liftOn {n₁ = n₁} {n₂ = 𝐒 n₂} {As}{Bs}{C}) where
--   postulate test : ∀{n}{A}{Bs : Type{ℓ} ^ n}{C} → (Bs ⇉ A) → (A → (Bs ⇉ C)) → (Bs ⇉ C)
-- 

{- TODO: Does not work because of →→ being defined by a head tail list
liftOn {n₁ = n₁} {n₂ = 𝟎} = const
liftOn {n₁ = n₁} {n₂ = 𝐒 𝟎} = _∘ᵣ_
liftOn {n₁ = n₁} {n₂ = 𝐒(𝐒 𝟎)} = {!!}
liftOn {n₁ = n₁} {n₂ = 𝐒(𝐒(𝐒 n₂))} {As}{B₁ , (B₂ , Bs)}{C} = {!_∘ᵣ_ {n = 𝐒(𝐒(𝐒 n₂))} (liftOn {n₁ = n₁}{n₂ = 2} (_$₁_)) (liftOn {n₁ = n₁}{n₂ = 𝐒(𝐒 n₂)} {As}{B₂ , Bs}{_})!}
-}
