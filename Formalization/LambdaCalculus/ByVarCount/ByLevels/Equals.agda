module Formalization.LambdaCalculus.ByVarCount.ByLevels.Equals where

open import Formalization.LambdaCalculus.ByVarCount
import      Lvl
open import Numeral.Finite
open import Numeral.Finite.Functions
open import Numeral.Natural
open import Structure.Relator.Properties
open import Type
open import Type.Identity
open import Type.Identity.Proofs

private variable A B N : ℕ
private variable a : 𝕟(A)
private variable b : 𝕟(B)
private variable n : 𝕟(N)
private variable t t₁ t₂ t₃ f₁ f₂ x₁ x₂ body₁ body₂ : Term(A)

-- When two terms should behave the same when interpreting terms by levels.
data _≡_ : Term(A) → Term(B) → Type{Lvl.𝟎} where
  Apply    : (f₁ ≡ f₂) → (x₁ ≡ x₂) → (Apply f₁ x₁ ≡ Apply f₂ x₂)
  Abstract : (body₁ ≡ body₂)  → (Abstract body₁ ≡ Abstract body₂)
  Var      : Id (boundDiff a) (boundDiff b) → (Var a ≡ Var b)

refl : t ≡ t
refl {t = Apply t₁ t₂} = Apply refl refl
refl {t = Abstract t}  = Abstract refl
refl {t = Var i}       = Var(reflexivity(Id))

sym : t₁ ≡ t₂ → t₂ ≡ t₁
sym (Apply p q)  = Apply (sym p) (sym q)
sym (Abstract p) = Abstract (sym p)
sym (Var p)      = Var (symmetry(Id) p)

trans : t₁ ≡ t₂ → t₂ ≡ t₃ → t₁ ≡ t₃
trans (Apply p₁ p₂) (Apply q₁ q₂) = Apply (trans p₁ q₁) (trans p₂ q₂)
trans (Abstract p)  (Abstract q)  = Abstract (trans p q)
trans (Var p)       (Var q)       = Var (transitivity(Id) p q)

-- open import Formalization.LambdaCalculus.ByVarCount.Functions
{-
var-𝐒-identity : var-𝐒 t ≡ t
var-𝐒-identity {t = Apply t₁ t₂} = Apply var-𝐒-identity var-𝐒-identity
var-𝐒-identity {t = Abstract t}  = Abstract var-𝐒-identity
var-𝐒-identity {t = Var 𝟎}       = Var intro
var-𝐒-identity {t = Var (𝐒 x)}   = Var intro
-}

{- TODO: Not true in general because free variables can be renamed. Should this be encountered for by the relation?
varShift𝐒-identity : varShift𝐒 n t ≡ t
varShift𝐒-identity {t = Apply t₁ t₂} = Apply varShift𝐒-identity varShift𝐒-identity
varShift𝐒-identity {t = Abstract t}  = Abstract varShift𝐒-identity
varShift𝐒-identity {n = 𝟎} {t = Var 𝟎} = {!!}
varShift𝐒-identity {n = 𝟎} {t = Var (𝐒 v)} = {!!}
varShift𝐒-identity {n = 𝐒 n} {t = Var 𝟎} = {!!}
varShift𝐒-identity {n = 𝐒 n} {t = Var (𝐒 v)} = {!!}
-}
