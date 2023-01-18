{-# OPTIONS --with-K #-}
module Type.Identity.Heterogenous.Proofs where

open import Functional
import      Lvl
open import Syntax.Function
open import Type
open import Type.Identity.Heterogenous

private variable ℓ ℓ₁ ℓ₂ ℓₗ : Lvl.Level
private variable T A X Y : Type{ℓ}
private variable B : A → Type{ℓ}
private variable x y : T

-- TODO: Possible without axiom K
singleton : ∀{e : HId x y} → HId e (intro{x = x})
singleton {e = intro} = intro

-- Note: Not possible without axiom K.
elim' : (P : ∀{X Y : Type{ℓ}}(x : X) → (y : Y) → (HId x y) → Type{ℓₗ}) → (∀{T : Type{ℓ}}{x : T} → P x x intro) → (∀{X Y : Type{ℓ}}{x : X}{y : Y} → (e : HId x y) → P x y e)
elim' _ p intro = p

-- Note: Not possible without axiom K.
elim : (P : (x : T) → (y : T) → (HId x y) → Type{ℓₗ}) → (∀{x} → P x x intro) → (∀{x y : T} → (e : HId x y) → P x y e)
elim _ p intro = p

-- Note: Not possible without axiom K.
elimFixed : ∀{x : T} → (P : (y : T) → (HId x y) → Type{ℓₗ}) → P x intro → (∀{y : T} → (e : HId x y) → P y e)
elimFixed _ p intro = p

compute : ∀{x : T} → (P : (y : T) → HId x y → Type{ℓₗ}) → (p : P x intro) → HId (elimFixed(P) p intro) p
compute _ _ = intro

subRefl : (_▫_ : T → T → Type{ℓ}) → (∀{x} → (x ▫ x)) → (∀{x y} → HId x y → (x ▫ y))
subRefl(_▫_) refl {x} xy = elimFixed(y ↦ xy ↦ (x ▫ y)) refl xy

substitute₁ : (P : T → Type{ℓ}) → (∀{x y} → HId x y → (P(x) → P(y)))
substitute₁ P = subRefl((_→ᶠ_) on₂ P) id

congruence₁ : (f : (a : A) → B(a)) → ∀{x y : A} → HId x y → HId (f(x)) (f(y))
congruence₁ f {x}{y} = elimFixed(y ↦ xy ↦ HId (f(x)) (f(y))) intro

open import Type.Identity
open import Structure.Relator.Properties

instance
  Id-HId-sub : Id{T = T} ⊆₂ HId
  Id-HId-sub = intro \{intro → intro}

-- open import Structure.Type.Identity
-- IdentityKEliminator(Id{T = T})

{-
module _ where
  open import Type.Identity
  open import Type.Identity.Proofs
  open import Structure.Relator

  test : Id x y → HId x y
  test intro = intro

  test2 : HId x y → Id (Type.of x) (Type.of y)
  test2 intro = intro

  subst : (P : T → Type{ℓ}) → Id x y → P(x) → P(y)
  subst _ intro p = p

  test3 : HId x y → Id (Type.of x) (Type.of y)
  test3 intro = intro

  test4 : (e : HId x y) → Id x (substitute₁ᵣ())
  test4 intro = intro
-}
