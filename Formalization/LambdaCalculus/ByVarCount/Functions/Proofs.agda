module Formalization.LambdaCalculus.ByVarCount.Functions.Proofs where

open import Data.Option.Proofs
open import Formalization.LambdaCalculus.ByVarCount
open import Formalization.LambdaCalculus.ByVarCount.Functions
open import Functional
open import Numeral.Finite as 𝕟 using (𝕟 ; 𝟎 ; 𝐒)
import      Numeral.Finite.Bound as 𝕟
import      Numeral.Finite.Bound.Proofs as 𝕟
open import Numeral.Finite.Oper.Proofs as Option
import      Numeral.Finite.Relation.Order as 𝕟
import      Numeral.Finite.Relation.Order.Proofs as 𝕟
open import Numeral.Natural
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator.Properties
open import Type

private variable d d₁ d₂ : ℕ
private variable i i₁ i₂ n : 𝕟(d)
private variable x y : Term(d)

substituteVar-identity : substituteVar i x (Var i) ≡ x
substituteVar-identity {i = i}{x = x} = partialMap-none-value ⦃ none = shift𝐏-is-none-simple{c = i}{x = i} (𝕟.[≡]-reflexivity-raw {a = i}) ⦄

open import Data.Boolean.Stmt
open import Logic.Propositional

IsVars-sub : ∀{ℓ₁ ℓ₂}{P : ∀{d} → 𝕟(d) → Type{ℓ₁}}{Q : ∀{d} → 𝕟(d) → Type{ℓ₂}}{d}{x : Term(d)} → (∀{d}{n : 𝕟(d)} → P(n) → Q(n)) → (IsVars P x → IsVars Q x)
IsVars-sub {x = Apply f x}  pq = [∧]-map (IsVars-sub {x = f} pq) (IsVars-sub {x = x} pq)
IsVars-sub {x = Abstract b} pq = IsVars-sub {x = b} pq
IsVars-sub {x = Var x}      pq = pq

substituteVar-varShift𝐒-identity : let _ = x in (IsVars(𝕟._≥ i₁) x ∨ (i₁ 𝕟.≤ i₂)) → (IsVars(𝕟._≥ i₂) x ∨ (i₁ 𝕟.≥ i₂)) → (substituteVar i₁ y (varShift𝐒 i₂ x) ≡ x)
substituteVar-varShift𝐒-identity {d} {Apply f x} {i₁}{i₂}{y} p1 p2
  rewrite substituteVar-varShift𝐒-identity {d}{f}{i₁}{i₂}{y} ([∨]-elim2 [∧]-elimₗ id p1) ([∨]-elim2 [∧]-elimₗ id p2)
  rewrite substituteVar-varShift𝐒-identity {d}{x}{i₁}{i₂}{y} ([∨]-elim2 [∧]-elimᵣ id p1) ([∨]-elim2 [∧]-elimᵣ id p2)
  = [≡]-intro
substituteVar-varShift𝐒-identity {d} {Abstract x} {i₁}{i₂}{y} p1 p2
  rewrite symmetry(_≡_) (𝕟.[⋚?]-of-bound-𝐒 {n₁ = i₁}{n₂ = i₂})
  rewrite substituteVar-varShift𝐒-identity {𝐒(d)}{x}{𝕟.bound-𝐒(i₁)}{𝕟.bound-𝐒(i₂)}{varShift𝐒 i₁ y}
    ([∨]-elim2 (IsVars-sub {x = x} (\{_}{i} ord → 𝕟.[≥][≡]-subtransitivityᵣ-raw {a = i}{b = i₁}{c = 𝕟.bound-𝐒(i₁)} ord (𝕟.[≡]-symmetry-raw {a = 𝕟.bound-𝐒(i₁)}{b = i₁} (𝕟.bound-𝐒-identity {n = i₁})))) id p1)
    ([∨]-elim2 (IsVars-sub {x = x} (\{_}{i} ord → 𝕟.[≥][≡]-subtransitivityᵣ-raw {a = i}{b = i₂}{c = 𝕟.bound-𝐒(i₂)} ord (𝕟.[≡]-symmetry-raw {a = 𝕟.bound-𝐒(i₂)}{b = i₂} (𝕟.bound-𝐒-identity {n = i₂})))) id p2)
  = [≡]-intro
substituteVar-varShift𝐒-identity {𝐒 d} {Var v} {i₁}{i₂}{y} p1 p2
  rewrite shift𝐏-shift𝐒-inverse{c₁ = i₁}{c₂ = i₂}{x = v} p1 p2
  = [≡]-intro

{-
-- Substituting the outer variable of `var-𝐒 x` yields `x`.
-- This is useful because `substituteVar0` uses `var-𝐒` in its definition.
substituteVar0-var-𝐒 : (substituteVar0 y (var-𝐒 x) ≡ x)
substituteVar0-var-𝐒 {d}{y}{Apply f x}  rewrite substituteVar0-var-𝐒 {d}{y}{f} rewrite substituteVar0-var-𝐒 {d}{y}{x} = [≡]-intro
substituteVar0-var-𝐒 {d}{y}{Abstract x} rewrite substituteVar0-var-𝐒 {𝐒 d}{var-𝐒 y}{x} = [≡]-intro
substituteVar0-var-𝐒 {_}{_}{Var 𝟎}      = [≡]-intro
substituteVar0-var-𝐒 {_}{_}{Var(𝐒 _)}   = [≡]-intro
{-# REWRITE substituteVar0-var-𝐒 #-}
-}

{-
depth-𝐒-isOutermostIndexFree : IsOutermostIndexFree(depth-𝐒(x))
depth-𝐒-isOutermostIndexFree {x = Apply f x} = IsTrue.[∧]-intro (depth-𝐒-isOutermostIndexFree {x = f}) (depth-𝐒-isOutermostIndexFree {x = x})
depth-𝐒-isOutermostIndexFree {x = Abstract x} = depth-𝐒-isOutermostIndexFree {x = x}
depth-𝐒-isOutermostIndexFree {𝐒 𝟎}   {x = Var 𝟎}    = <>
depth-𝐒-isOutermostIndexFree {𝐒(𝐒 d)}{x = Var 𝟎}    = <>
depth-𝐒-isOutermostIndexFree {𝐒(𝐒 d)}{x = Var(𝐒 v)} = depth-𝐒-isOutermostIndexFree {𝐒 d}{x = Var v}

var-𝐒-isOutermostLevelFree : IsOutermostLevelFree(var-𝐒(x))
var-𝐒-isOutermostLevelFree {x = Apply f x} = IsTrue.[∧]-intro (var-𝐒-isOutermostLevelFree {x = f}) (var-𝐒-isOutermostLevelFree {x = x})
var-𝐒-isOutermostLevelFree {x = Abstract x} = var-𝐒-isOutermostLevelFree {x = x}
var-𝐒-isOutermostLevelFree {x = Var 𝟎} = <>
var-𝐒-isOutermostLevelFree {x = Var (𝐒 v)} = <>

var-𝐒-substituteVar0 : ⦃ IsOutermostLevelFree x ⦄ → (var-𝐒(substituteVar0 y x) ≡ substituteVar0 (var-𝐒 y) (var-𝐒 x))
var-𝐒-substituteVar0 {d}  {Apply f x} {y} ⦃ free ⦄
  rewrite var-𝐒-substituteVar0 {d}{f}{y} ⦃ IsTrue.[∧]-elimₗ free ⦄
  rewrite var-𝐒-substituteVar0 {d}{x}{y} ⦃ IsTrue.[∧]-elimᵣ free ⦄
  = [≡]-intro
var-𝐒-substituteVar0 {d}  {Abstract x}{y} ⦃ free ⦄
  rewrite var-𝐒-substituteVar0 {𝐒 d}{x}{var-𝐒 y} ⦃ free ⦄
  = [≡]-intro
var-𝐒-substituteVar0 {d}  {Var 𝟎}     {y} ⦃ ⦄
var-𝐒-substituteVar0 {𝐒 d}{Var(𝐒 v)}  {y} = [≡]-intro
-}

-- import Data.Option.Proofs as Option
-- import Numeral.Finite.Oper.Proofs as 𝕟
-- postulate substituteVarMax-depth-𝐒 : (substituteVarMax y (depth-𝐒 x) ≡ x)
-- substituteVarMax-depth-𝐒 {d} {y} {Apply f x} rewrite substituteVarMax-depth-𝐒 {d}{y}{f} rewrite substituteVarMax-depth-𝐒 {d}{y}{x} = [≡]-intro
-- substituteVarMax-depth-𝐒 {d} {y} {Abstract x} rewrite substituteVarMax-depth-𝐒 {𝐒 d}{depth-𝐒 y}{x} = [≡]-intro
-- substituteVarMax-depth-𝐒 {d} {y} {Var x} = {!Option.partialMap-some-value {def = y}{f = Var} ⦃ some = 𝕟.shift-is-some{c = 𝕟.maximum{𝐒(d)}}{x = 𝕟.bound-𝐒(x)} ? ⦄!}

{-
open import Data.Option as Option using (Option)
import      Data.Option.Functions as Option
open import Data.Option.Quantifiers
open import Logic.Propositional
import      Numeral.Finite.Functions as 𝕟
open import Numeral.Finite.Functions.Proofs
import      Numeral.Finite.Relation as 𝕟
minVar : Term(d) → Option(𝕟(d))
minVar(Apply f x)     = Option.andCombine 𝕟.min₌ (minVar f) (minVar x)
minVar(Abstract body) = (minVar body) Option.andThen \{𝟎 → Option.None ; (𝐒(m)) → Option.Some(m)}
minVar(Var i)         = Option.Some(i)

var-𝐒-substituteVar0 : ∀ₒₚₜ(minVar x) 𝕟.Positive → (var-𝐒(substituteVar0 y x) ≡ x)
var-𝐒-substituteVar0 {d}     {Apply f x}     {y} p
  rewrite var-𝐒-substituteVar0 {d}{f}{y} {!!} -- [∧]-elimₗ (min₌-positive{x = minVar f}{y = minVar x} p)
  rewrite var-𝐒-substituteVar0 {d}{x}{y} {!!} -- [∧]-elimᵣ (min₌-positive{x = minVar f}{y = minVar x} p)
  = [≡]-intro
var-𝐒-substituteVar0 {d}     {Abstract body} {y} p
  rewrite var-𝐒-substituteVar0{𝐒(d)}{body}{var-𝐒(y)} {!!}
  = [≡]-intro
var-𝐒-substituteVar0 {.(𝐒 _)}{Var (𝐒 𝟎)}      {y} p = [≡]-intro
var-𝐒-substituteVar0 {.(𝐒 _)}{Var (𝐒(𝐒 i))}   {y} p = [≡]-intro
{-var-𝐒-substituteVar0 {d}{y} {Apply f x}     _ rewrite var-𝐒-substituteVar0 {d}{y}{f} rewrite var-𝐒-substituteVar0 {d}{y}{x} = [≡]-intro
var-𝐒-substituteVar0 {d}{y} {Abstract body} _ rewrite var-𝐒-substituteVar0 {𝐒 d}{var-𝐒 y}{body}= [≡]-intro
var-𝐒-substituteVar0 {d}{y} {Var 𝟎} p = {!!}
var-𝐒-substituteVar0 {.(𝐒 _)} {y} {Var (𝐒 𝟎)} _ = [≡]-intro
var-𝐒-substituteVar0 {.(𝐒 _)} {y} {Var (𝐒 (𝐒 i))} _ = [≡]-intro
-}
-}
