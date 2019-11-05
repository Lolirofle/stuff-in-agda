module Functional.Multi{ℓ} where

open import Data
open import Functional using (_→ᶠ_ ; id) renaming (const to constᶠ ; _∘_ to _∘ᶠ_ ; apply to applyᶠ ; swap to swapᶠ)
import      Lvl
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Natural
open import Syntax.Function
open import Syntax.Number
open import Type{ℓ}

-- TODO: Take some ideas from https://github.com/agda/agda/commit/b6124012acf59d556f69a99c8fa03ec07b1ad1ff

-- Essentially: (A,B,C,D,..) [→] R = A → (B → (C → (D → (.. → R)))) = (A → B → C → D → .. → R)
_[→]_ : ∀{n : ℕ} → (𝕟(n) → Type) → Type → Type
_[→]_ {𝟎}    _  B = B
_[→]_ {𝐒(n)} As B = As(𝟎) → ((As ∘ᶠ 𝐒) [→] B)

{-
pushₗ : (A → (As [→] B)) → ((A ⊰ As) [→] B)
popₗ : (As [→] B) → (As(𝟎) → ((As ∘ᶠ 𝐒) [→] B))
pushᵣ : (As [→] (A → B)) → (postpend A As [→] B)
popᵣ : 
-}

uncurry : ∀{n}{As : 𝕟(n) → Type}{B : Type} → (As [→] B) → (((i : 𝕟(n)) → As(i)) → B)
uncurry {𝟎}   f _ = f
uncurry {𝐒 n} f x = uncurry(f(x(𝟎))) (i ↦ x(𝐒(i)))

curry : ∀{n}{As : 𝕟(n) → Type}{B : Type} → (((i : 𝕟(n)) → As(i)) → B) → (As [→] B)
curry {𝟎}   f    = f \()
curry {𝐒 n} f x₁ = curry(x ↦ f(\{𝟎 -> x₁ ; (𝐒(i)) -> x(i)}))

applyCoordVec : ∀{n}{As : 𝕟(n) → Type}{B : Type} → ((i : 𝕟(n)) → As(i)) → (As [→] B) → B
applyCoordVec = swapᶠ uncurry

const : ∀{n}{As : 𝕟(n) → Type}{B : Type} → B → (As [→] B)
const{𝟎}    = id
const{𝐒(n)} = constᶠ ∘ᶠ const{n}

swap : ∀{a b}{As : 𝕟(a) → Type}{Bs : 𝕟(b) → Type}{C : Type} → (As [→] (Bs [→] C)) → (Bs [→] (As [→] C))
swap {a} {𝟎} {As} {Bs} {C} bsasc = {!bsasc!}
swap {a} {𝐒 b} {As} {Bs} {C} bsasc = {!!}

apply : ∀{n}{As : 𝕟(n) → Type}{B : Type} → (As [→] ((As [→] B) → B))
apply {𝟎}      = id
apply {𝐒 n} x₁ = {!apply {n} x₁!}

{-
apply 0 = id
apply 1 x = \f -> f x = _$ x
apply 2 x y = \f -> (f x) y = \f -> (($ x) f) y = 
apply 3 x y z = \f -> ((f x) y) z = \f -> (($ x) f) y
-}

-- Essentially:
--   f ∘ᵣ g = (((f ∘_) ∘_) ∘_) ..
--   ((((f ∘ᵣ g) x₁) x₂) x₃) .. = f((((g x₁) x₂) x₃) ..)
--   (f ∘ᵣ g) x₁ x₂ x₃ .. = f(g x₁ x₂ x₃ ..)
_∘ᵣ_ : ∀{n}{As : 𝕟(n) → Type}{B : Type}{C : Type} → (B → C) → (As [→] B) → (As [→] C)
_∘ᵣ_ {𝟎}        f = f
_∘ᵣ_ {𝐒(n)}{As} f = (_∘ᵣ_ {n}{As ∘ᶠ 𝐒} f) ∘ᶠ_

-- Essentially:
--   (f ∘ₗ g₁ g₂ g₃ ..) x = f (g₁ x) (g₂ x) (g₃ x) ..
_∘ₗ : ∀{n}{A : Type}{Bs : 𝕟(n) → Type}{C : Type} → (Bs [→] C) → (((A →ᶠ_) ∘ᶠ Bs) [→] (A → C))
_∘ₗ {𝟎}   f    = constᶠ f
_∘ₗ {𝐒 n} f g₁ = {!!}
-- Note: f ∘ g₁ : A → ((Bs ∘ 𝐒) [→] C)
-- Goal: ((A →_) ∘ Bs ∘ 𝐒) [→] (A → C)

-- Essentially:
--   (f on g) x₁ x₂ x₃ .. = f (g x₁) (g x₂) (g x₃) ..
-- _on_ : ∀{n} → ()

-- Essentially:
--   (f ∘ g₁ g₂ g₃ ..) x₁ x₂ x₃ .. = f (g₁ x₁ x₂ x₃ ..) (g₂ x₁ x₂ x₃ ..) (g₃ x₁ x₂ x₃ ..) ..

-- Essentially:
--   (f ∘ g₁ g₂ g₃ ..) x₁ x₂ x₃ .. = f (g₁ x₁) (g₂ x₂) (g₃ x₃) ..
_∘ₗₑ_ : ∀{n}{As : 𝕟(n) → Type}{Bs : 𝕟(n) → Type}{C : Type} → (Bs [→] C) → ((n ↦ (As(n) → Bs(n))) [→] (As [→] C))
_∘ₗₑ_ {𝟎}     = id
_∘ₗₑ_ {𝐒 𝟎}   = _∘ᶠ_
_∘ₗₑ_ {𝐒(𝐒 n)} f = (_∘ᶠ unknown{n}) ∘ᵣ (swap(_∘ᶠ_) ∘ᵣ (_∘ₗₑ_ {𝐒 n} {!f!})) where
  unknown : ∀{n}{As : 𝕟₌(n) → Type}{B : Type}{C : Type} → (As(maximum) → B) → ((As ∘ᶠ bound-𝐒) [→] (B → C)) → (As [→] C)
  unknown{𝟎}    = swap(_∘ᶠ_)
  unknown{𝐒(n)}{As} = (_∘ᶠ_) ∘ᶠ unknown{n}{As ∘ᶠ 𝐒}


{-
postulate A B C D : Type{ℓ₁}
postulate E : Type{ℓ₁ Lvl.⊔ ℓ₂}
f : 𝕟₌(𝐒(𝐒(𝐒(𝟎)))) → Type{ℓ₁}
f(𝟎)          = A
f(𝐒(𝟎))       = B
f(𝐒(𝐒(𝟎)))    = C
f(𝐒(𝐒(𝐒(𝟎)))) = D

test : (f [→] E) → (A → (B → (C → (D → E))))
test x = x
-}
