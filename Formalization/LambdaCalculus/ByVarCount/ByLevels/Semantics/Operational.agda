-- Definitions of reduction results for normalization of terms.
-- "Big-step" semantics.
-- Source: "Demonstrating Lambda Calculus Reduction, Peter Sestoft" (2022-12-01) [https://www.itu.dk/~sestoft/papers/sestoft-lamreduce.pdf]
module Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Operational where

import      Lvl
open import Data
open import Data.Boolean.Stmt
open import Formalization.LambdaCalculus.ByVarCount
open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Operators
open import Formalization.LambdaCalculus.ByVarCount.Functions
open import Numeral.Finite
open import Numeral.Natural
open import Type

private variable d db : ℕ
private variable i : 𝕟(d)
private variable f t x v vₓ vf vf₁ vf₂ vb : Term(d)
private variable body : Term(db)

-- Operational semantics for the call-by-name strategy.
data _⇓ᶜⁿ_ : Term(d) → Term(d) → Type{Lvl.𝟎} where
  var   : (Var i ⇓ᶜⁿ Var i)
  abstr : (Abstract body ⇓ᶜⁿ Abstract body)
  apply : (f ⇓ᶜⁿ vf) → ⦃ IsFalse(isAbstract vf) ⦄ → (Apply f x ⇓ᶜⁿ Apply vf x)
  β     : (f ⇓ᶜⁿ Abstract body) → (substituteVar maximum x body ⇓ᶜⁿ v) → (Apply f x ⇓ᶜⁿ v)

-- Operational semantics for the call-by-value strategy.
data _⇓ᶜᵛ_ : Term(d) → Term(d) → Type{Lvl.𝟎} where
  var   : (Var i ⇓ᶜᵛ Var i)
  abstr : (Abstract body ⇓ᶜᵛ Abstract body)
  apply : (f ⇓ᶜᵛ vf) → ⦃ IsFalse(isAbstract vf) ⦄ → (x ⇓ᶜᵛ vₓ) → (Apply f x ⇓ᶜᵛ Apply vf vₓ)
  β     : (f ⇓ᶜᵛ Abstract body) → (x ⇓ᶜᵛ vₓ) → (substituteVar maximum vₓ body ⇓ᶜᵛ v) → (Apply f x ⇓ᶜᵛ v)

-- Operational semantics for the normal order strategy.
data _⇓ⁿᵒ_ : Term(d) → Term(d) → Type{Lvl.𝟎} where
  var   : (Var i ⇓ⁿᵒ Var i)
  abstr : (body ⇓ⁿᵒ vb) → (Abstract body ⇓ⁿᵒ Abstract vb)
  apply : (f ⇓ᶜⁿ vf₁) → ⦃ IsFalse(isAbstract vf₁) ⦄ → (vf₁ ⇓ⁿᵒ vf₂) → (x ⇓ⁿᵒ vₓ) → (Apply f x ⇓ⁿᵒ Apply vf₂ vₓ)
  β     : (f ⇓ᶜⁿ Abstract body) → (substituteVar maximum x body ⇓ⁿᵒ v) → (Apply f x ⇓ⁿᵒ v)

-- Operational semantics for the applicative order strategy.
data _⇓ᵃᵒ_ : Term(d) → Term(d) → Type{Lvl.𝟎} where
  var   : (Var i ⇓ᵃᵒ Var i)
  abstr : (body ⇓ᵃᵒ vb) → (Abstract body ⇓ᵃᵒ Abstract vb)
  apply : (f ⇓ᵃᵒ vf) → ⦃ IsFalse(isAbstract vf) ⦄ → (x ⇓ᵃᵒ vₓ) → (Apply f x ⇓ᵃᵒ Apply vf vₓ)
  β     : (f ⇓ᵃᵒ Abstract body) → (x ⇓ᵃᵒ vₓ) → (substituteVar maximum vₓ body ⇓ᵃᵒ v) → (Apply f x ⇓ᵃᵒ v)

-- Operational semantics for the applicative order strategy.
data _⇓ʰˢ_ : Term(d) → Term(d) → Type{Lvl.𝟎} where
  var   : (Var i ⇓ʰˢ Var i)
  abstr : (body ⇓ʰˢ vb) → (Abstract body ⇓ʰˢ Abstract vb)
  apply : (f ⇓ʰˢ vf) → ⦃ IsFalse(isAbstract vf) ⦄ → (Apply f x ⇓ʰˢ Apply vf x)
  β     : (f ⇓ʰˢ Abstract body) → (substituteVar maximum x body ⇓ʰˢ v) → (Apply f x ⇓ʰˢ v)


open import Data.Boolean.Stmt.Logic
open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Operators.Normal

[⇓ᶜⁿ]-whnf : (t ⇓ᶜⁿ v) → IsTrue(isNormalForm βWHNF v)
[⇓ᶜⁿ]-whnf {v = Abstract _}         _         = <>
[⇓ᶜⁿ]-whnf {v = Var v}              _         = <>
[⇓ᶜⁿ]-whnf {v = Apply f x}          (β _ q)   = [⇓ᶜⁿ]-whnf q
[⇓ᶜⁿ]-whnf {v = Apply(Apply _ _) _} (apply p) = [⇓ᶜⁿ]-whnf p
[⇓ᶜⁿ]-whnf {v = Apply(Var _) _}     (apply _) = <>

{-
[⇓ⁿᵒ]-nf : (t ⇓ⁿᵒ v) → IsTrue(isNormalForm βNF v)
[⇓ⁿᵒ]-nf {v = Abstract _} (abstr p) = [⇓ⁿᵒ]-nf p
[⇓ⁿᵒ]-nf {v = Var v}               _         = <>
[⇓ⁿᵒ]-nf {v = Apply f x}           (β _ q)   = [⇓ⁿᵒ]-nf q
[⇓ⁿᵒ]-nf {v = Abstract _}          (β _ q)   = [⇓ⁿᵒ]-nf q
[⇓ⁿᵒ]-nf {v = Apply(Apply _ _) _}  (apply p q r) = IsTrue.[∧]-intro ([⇓ⁿᵒ]-nf q) ([⇓ⁿᵒ]-nf r)
[⇓ⁿᵒ]-nf {v = Apply(Var _) _}      (apply _ _ r) = [⇓ⁿᵒ]-nf r
[⇓ⁿᵒ]-nf {v = Apply (Abstract _) _} (apply p (β q r) s) = {!!} -- TODO: Is this possible? For call-by-name to get stuck but normal order continuing
-}

[⇓ᶜᵛ]-wnf : (t ⇓ᶜᵛ v) → IsTrue(isNormalForm βWNF v)
[⇓ᶜᵛ]-wnf {v = Abstract _}          _         = <>
[⇓ᶜᵛ]-wnf {v = Var v}               _         = <>
[⇓ᶜᵛ]-wnf {v = Apply f x}           (β p q r)   = [⇓ᶜᵛ]-wnf r
[⇓ᶜᵛ]-wnf {v = Apply(Apply _ _) _}  (apply p q) = IsTrue.[∧]-intro ([⇓ᶜᵛ]-wnf p) ([⇓ᶜᵛ]-wnf q)
[⇓ᶜᵛ]-wnf {v = Apply(Var _) _}      (apply p q) = [⇓ᶜᵛ]-wnf q

[⇓ᵃᵒ]-nf : (t ⇓ᵃᵒ v) → IsTrue(isNormalForm βNF v)
[⇓ᵃᵒ]-nf {v = Var _}              _           = <>
[⇓ᵃᵒ]-nf {v = Abstract x}         (abstr p)   = [⇓ᵃᵒ]-nf p
[⇓ᵃᵒ]-nf {v = Abstract x}         (β p q r)   = [⇓ᵃᵒ]-nf r
[⇓ᵃᵒ]-nf {v = Apply f x}          (β p q r)   = [⇓ᵃᵒ]-nf r
[⇓ᵃᵒ]-nf {v = Apply(Apply _ _) _} (apply p q) = IsTrue.[∧]-intro ([⇓ᵃᵒ]-nf p) ([⇓ᵃᵒ]-nf q)
[⇓ᵃᵒ]-nf {v = Apply(Var _) _}     (apply p q) = [⇓ᵃᵒ]-nf q

[⇓ʰˢ]-nf : (t ⇓ʰˢ v) → IsTrue(isNormalForm βHNF v)
[⇓ʰˢ]-nf {v = Abstract _}         (abstr p) = [⇓ʰˢ]-nf p
[⇓ʰˢ]-nf {v = Var x}              _         = <>
[⇓ʰˢ]-nf {v = Abstract _}         (β p q)   = [⇓ʰˢ]-nf q
[⇓ʰˢ]-nf {v = Apply _ _}          (β p q)   = [⇓ʰˢ]-nf q
[⇓ʰˢ]-nf {v = Apply(Apply _ _) _} (apply p) = [⇓ʰˢ]-nf p
[⇓ʰˢ]-nf {v = Apply(Var _) _}     (apply p) = <>
