module Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction.Proofs.Properties where

open import Data
open import Data.Boolean.Stmt
import      Lvl
open import Formalization.LambdaCalculus.ByVarCount
open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction
open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction.Proofs
open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.Combinators
open        Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.Combinators.Proofs
open import Formalization.LambdaCalculus.ByVarCount.Functions
open import Formalization.LambdaCalculus.ByVarCount.Syntax.ExplicitLambda
open import Numeral.Finite
open import Numeral.Natural
open import Relator.ReflexiveTransitiveClosure
import      Structure.Function.Names as Names
open import Structure.Function

private variable d d₁ d₂ : ℕ
private variable n : 𝕟(d)
private variable f g x y z x₁ x₂ y₁ y₂ z₁ z₂ : Term(d)


-- open import Structure.Relator.Properties
open import Functional using (_∘_)
open import Logic.Predicate
open import Logic.Propositional hiding (_←_)
open import ReductionSystem
open import Relator.Equals
open import Syntax.Number

open import Graph.Walk
open import Syntax.Transitivity

Ω-no-normal-form : ¬ NormalForm(_β⇴_)(Ω)
Ω-no-normal-form (intro p) = p(Ω-self-reduces)

-- Multiple reduction rules may be applicable on a term.
-- Reduction is not deterministic unless restricted to certain reduction orders.
[β⇴]-non-deterministic : ¬ Deterministic(_β⇴_ {d})
[β⇴]-non-deterministic d@{𝟎}   det with () ← det {((𝜆 d 0) ← (𝜆 d 0)) ← ((𝜆 d 0) ← (𝜆 d 0))} (cong-applyₗ β) (cong-applyᵣ β)
[β⇴]-non-deterministic d@{𝐒 _} det with () ← det {((𝜆 d 0) ← (𝜆 d 0)) ← ((𝜆 d 0) ← (𝜆 d 0))} (cong-applyₗ β) (cong-applyᵣ β)

[β⇴]-callByName-deterministic : Deterministic(\a b → ∃(IsTrue ∘ isCallByNameβ{d}{a}{b}))
[β⇴]-callByName-deterministic ([∃]-intro β) ([∃]-intro β) = [≡]-intro
[β⇴]-callByName-deterministic ([∃]-intro (cong-applyₗ p)) ([∃]-intro (cong-applyₗ q))
  rewrite [β⇴]-callByName-deterministic ([∃]-intro p) ([∃]-intro q)
  = [≡]-intro

{-
[β⇴*]-not-weaklyNormalizing : ¬ WeaklyNormalizing(_β⇴_ {d})
[β⇴*]-not-weaklyNormalizing {𝟎} normalizing =
  let [∃]-intro norm ⦃ p ⦄ = normalizing{Ω}
      open _normalizes-to_
  in {!normalForm([∃]-proof (normalizing{Ω}))!}
[β⇴*]-not-weaklyNormalizing {𝐒 d} norm = {!!}
-}

-- TODO: Move
open import Type

-- Parallel reduction.
data _‖⇴_ {d} : Term(d) → Term(d) → Type{Lvl.𝟎} where
  var   : ∀{v} → (Var v ‖⇴ Var v)
  apply : ∀{f g x y} → (f ‖⇴ g) → (x ‖⇴ y) → (Apply f x ‖⇴ Apply g y)
  abstr : ∀{f g} → (f ‖⇴ g) → (Abstract f ‖⇴ Abstract g)
  β     : ∀{x₁ y₁ x₂ y₂} → (x₁ ‖⇴ x₂) → (y₁ ‖⇴ y₂) → (Apply(Abstract x₁) y₁ ‖⇴ substituteVar maximum y₂ x₂)

_‖⇴*_ = \{d} → Walk(_‖⇴_ {d})

[‖⇴]-reflexivity-raw : ∀{x : Term(d)} → (x ‖⇴ x)
[‖⇴]-reflexivity-raw {x = Apply _ _}  = apply [‖⇴]-reflexivity-raw [‖⇴]-reflexivity-raw
[‖⇴]-reflexivity-raw {x = Abstract _} = abstr [‖⇴]-reflexivity-raw
[‖⇴]-reflexivity-raw {x = Var _}      = var

-- [‖⇴]-transitivity-raw : (x ‖⇴ y) → (y ‖⇴ z) → (x ‖⇴ z)
-- [‖⇴]-transitivity-raw p q = {!!}

private variable n₁ n₂ n₃ n₄ : 𝕟(d)
-- import Numeral.Finite.Relation.Order as 𝕟
open import Numeral.Finite.Bound
open import Numeral.Finite.Oper.Proofs
import      Numeral.Finite.Relation.Order as 𝕟

{-
varShift𝐒-preserve-self : (n₁ 𝕟.≥ n₂) → (varShift𝐒 (bound-𝐒(n₂)) (varShift𝐒 n₁ x) ≡ varShift𝐒 (𝐒 n₁) (varShift𝐒 n₂ x))
varShift𝐒-preserve-self {n₁ = n₁}{n₂ = n₂}{Apply f x} ord
  rewrite varShift𝐒-preserve-self {n₁ = n₁}{n₂ = n₂}{f} ord
  rewrite varShift𝐒-preserve-self {n₁ = n₁}{n₂ = n₂}{x} ord
  = [≡]-intro
varShift𝐒-preserve-self {n₁ = n₁}{n₂ = n₂} {Abstract x} ord
  rewrite varShift𝐒-preserve-self {n₁ = bound-𝐒(n₁)}{n₂ = bound-𝐒(n₂)}{x} {!!}
  = [≡]-intro
varShift𝐒-preserve-self {n₁ = 𝟎}   {n₂ = 𝟎}   {Var 𝟎}     _ = [≡]-intro
varShift𝐒-preserve-self {n₁ = 𝟎}   {n₂ = 𝟎}   {Var (𝐒 x)} _ = [≡]-intro
varShift𝐒-preserve-self {n₁ = 𝐒 n₁}{n₂ = 𝟎}   {Var 𝟎}     _ = [≡]-intro
varShift𝐒-preserve-self {n₁ = 𝐒 n₁}{n₂ = 𝟎}   {Var (𝐒 x)} _ = [≡]-intro
varShift𝐒-preserve-self {n₁ = 𝐒 n₁}{n₂ = 𝐒 n₂}{Var 𝟎}     _ = [≡]-intro
varShift𝐒-preserve-self {n₁ = 𝐒 n₁}{n₂ = 𝐒 n₂}{Var (𝐒 x)} ord
  rewrite shift𝐒-preserve-self-gt {n₁ = n₁}{n₂ = n₂}{x = x} ord
  = [≡]-intro

substituteVar-preserve-self : (n₁ 𝕟.≥ n₂) → (substituteVar n₁ x₁ (substituteVar (𝐒(n₂)) x₂ y) ≡ substituteVar n₂ (substituteVar n₁ x₁ x₂) (substituteVar (𝐒(n₁)) (varShift𝐒 n₂ x₁) y))
substituteVar-preserve-self {d} {n₁}{n₂} {x₁}{x₂} {Apply f x} ord
  rewrite substituteVar-preserve-self{d}{n₁}{n₂}{x₁}{x₂}{f} ord
  rewrite substituteVar-preserve-self{d}{n₁}{n₂}{x₁}{x₂}{x} ord
  = [≡]-intro
substituteVar-preserve-self {d} {n₁}{n₂} {x₁}{x₂} {Abstract b} ord
  rewrite substituteVar-preserve-self {𝐒 d} {bound-𝐒(n₁)}{bound-𝐒 n₂} {varShift𝐒 n₁ x₁}{varShift𝐒 (𝐒 n₂) x₂} {b} {!!}
  rewrite varShift𝐒-preserve-self {n₁ = n₁}{n₂ = n₂}{x₁} ord
  = {!!}
substituteVar-preserve-self {d} {n₁} {x₁} {n₂} {x₂} {Var v} = {!!}
-}

varShift𝐒-preserve-self : let _ = n₁ ;  _ = n₂ ;  _ = n₃ ;  _ = n₄ in (varShift𝐒 n₁ (varShift𝐒 n₂ x) ≡ varShift𝐒 n₃ (varShift𝐒 n₄ x))
varShift𝐒-preserve-self {d} {n₁} {n₂} {n₃} {n₄} {Apply f x}
  rewrite varShift𝐒-preserve-self {d} {n₁} {n₂} {n₃} {n₄} {f}
  rewrite varShift𝐒-preserve-self {d} {n₁} {n₂} {n₃} {n₄} {x}
  = [≡]-intro
varShift𝐒-preserve-self {d} {n₁} {n₂} {n₃} {n₄} {Abstract b}
  rewrite varShift𝐒-preserve-self {𝐒 d} {bound-𝐒(n₁)} {bound-𝐒(n₂)} {bound-𝐒(n₃)} {bound-𝐒(n₄)} {b}
  = [≡]-intro
varShift𝐒-preserve-self {.(𝐒 _)} {n₁} {n₂} {n₃} {n₄} {Var 𝟎} = {!!}
varShift𝐒-preserve-self {.(𝐒 _)} {n₁} {n₂} {n₃} {n₄} {Var (𝐒 v)} = {!!}

varShift𝐒-preserve-self-lt : (varShift𝐒 (bound-𝐒(n₁)) (varShift𝐒 n₁ x) ≡ varShift𝐒 n₂ (varShift𝐒 n₁ x))
varShift𝐒-preserve-self-lt {n₁ = n₁} {x = Apply f x} {n₂ = n₂}
  rewrite varShift𝐒-preserve-self-lt {n₁ = n₁}{x = f}{n₂ = n₂}
  rewrite varShift𝐒-preserve-self-lt {n₁ = n₁}{x = x}{n₂ = n₂}
  = [≡]-intro
varShift𝐒-preserve-self-lt {n₁ = n₁} {x = Abstract b} {n₂ = n₂}
  rewrite varShift𝐒-preserve-self-lt {n₁ = bound-𝐒(n₁)}{x = b}{n₂ = bound-𝐒(n₂)}
  = [≡]-intro
varShift𝐒-preserve-self-lt {n₁ = n₁} {x = Var v} {n₂ = n₂} = {!!}

varShift𝐒-of-substituteVar : let _ = n₁ in (n₂ 𝕟.≡ n₃) → varShift𝐒 n₁ (substituteVar n₂ x y) ≡ substituteVar n₃ (varShift𝐒 n₂ x) (varShift𝐒 n₄ y)

[‖⇴]-of-varShift𝐒 : (x₁ ‖⇴ x₂) → (varShift𝐒 n x₁ ‖⇴ varShift𝐒 n x₂)
[‖⇴]-of-varShift𝐒 var           = [‖⇴]-reflexivity-raw
[‖⇴]-of-varShift𝐒 (apply pf px) = apply ([‖⇴]-of-varShift𝐒 pf) ([‖⇴]-of-varShift𝐒 px)
[‖⇴]-of-varShift𝐒 (abstr px)    = abstr ([‖⇴]-of-varShift𝐒 px)
[‖⇴]-of-varShift𝐒 {n = n} (β {x₁} {y₁} {x₂ = x₂} {y₂} px py)
  rewrite varShift𝐒-of-substituteVar {n₁ = n}{n₂ = maximum}{n₃ = maximum}{x = y₂}{y = x₂}{n₄ = bound-𝐒 n} {!!}
  = _‖⇴_.β {x₁ = varShift𝐒 (bound-𝐒 n) x₁}{y₁ = varShift𝐒 n y₁}{x₂ = varShift𝐒 (bound-𝐒 n) x₂}{y₂ = varShift𝐒 maximum y₂} ([‖⇴]-of-varShift𝐒 px) {!!}
  -- _‖⇴_.β {x₁ = varShift𝐒 (bound-𝐒 n) x₁}{y₁ = varShift𝐒 n y₁}{x₂ = varShift𝐒 (bound-𝐒 n) x₂}{y₂ = varShift𝐒 maximum y₂} ([‖⇴]-of-varShift𝐒 px) {!!}
  -- ([‖⇴]-of-varShift𝐒 px) ([‖⇴]-of-varShift𝐒 py)
  -- _‖⇴_.β {x₁ = varShift𝐒 (bound-𝐒 n) x₁}{y₁ = varShift𝐒 n y₁}{x₂ = varShift𝐒 (bound-𝐒 n) x₂}{y₂ = varShift𝐒 n y₂} ([‖⇴]-of-varShift𝐒 px) ([‖⇴]-of-varShift𝐒 py)

-- Also called: Substitution lemma.
substituteVar-nested : (n₁ 𝕟.≡ n₂) → (n₃ 𝕟.≤ n₄) → (substituteVar n₁ x (substituteVar n₄ y₁ y₂) ≡ substituteVar n₃ (substituteVar n₁ x y₁) (substituteVar n₂ (varShift𝐒 n₁ x) y₂))
substituteVar-nested {d} {n₁} {n₂} {n₃} {n₄} {x} {y₁} {Apply y₂ y₃} pn pn2
  rewrite substituteVar-nested {n₁ = n₁}{n₂ = n₂}{n₃ = n₃}{n₄ = n₄}{x = x}{y₁ = y₁}{y₂ = y₂} pn {!!}
  rewrite substituteVar-nested {n₁ = n₁}{n₂ = n₂}{n₃ = n₃}{n₄ = n₄}{x = x}{y₁ = y₁}{y₂ = y₃} pn {!!}
  = [≡]-intro
substituteVar-nested {d} {n₁} {n₂} {n₃} {n₄} {x} {y₁} {Abstract y₂} pn pn2
  rewrite substituteVar-nested {𝐒 d} {bound-𝐒 n₁} {bound-𝐒 n₂} {bound-𝐒 n₃} {bound-𝐒 n₄} {varShift𝐒 n₁ x} {varShift𝐒 n₄ y₁} {y₂} {!!} {!!}
  rewrite varShift𝐒-of-substituteVar {n₁ = n₃}{n₂ = n₁}{n₃ = bound-𝐒 n₁}{x = x}{y = y₁}{n₄ = n₄} {!!}
  rewrite varShift𝐒-preserve-self-lt {n₁ = n₁}{x = x}{n₂ = n₂}
  = [≡]-intro
substituteVar-nested {d} {n₁} {n₂} {n₃} {n₄} {x} {y₁} {Var x₁} pn pn2 = {!!}

open import Logic.Propositional.Equiv
open import Structure.Relator
open import Relator.Equals.Proofs.Equiv

[‖⇴]-of-substituteVar : (x₁ ‖⇴ x₂) → (y₁ ‖⇴ y₂) → (substituteVar n x₁ y₁ ‖⇴ substituteVar n x₂ y₂)
[‖⇴]-of-substituteVar px var = {!!}
[‖⇴]-of-substituteVar px (apply pyₗ pyᵣ) = apply ([‖⇴]-of-substituteVar px pyₗ) ([‖⇴]-of-substituteVar px pyᵣ)
[‖⇴]-of-substituteVar px (abstr py) = abstr ([‖⇴]-of-substituteVar ([‖⇴]-of-varShift𝐒 px) py)
[‖⇴]-of-substituteVar {x₁ = x₁} {x₂} {n = n} px (β {y₁} {z₁} {y₂} {z₂} py pz) = substitute₂-₂ᵣ(_‖⇴_)(substituteVar n x₁ (𝜆 (𝐒 _) y₁ ← z₁)) {!substituteVar-nested ? ?!} (_‖⇴_.β {x₁ = substituteVar (bound-𝐒 n) (varShift𝐒 n x₁) y₁}{y₁ = substituteVar n x₁ z₁}{x₂ = substituteVar (bound-𝐒 n) (varShift𝐒 n x₂) y₂}{y₂ = substituteVar n x₂ z₂} ([‖⇴]-of-substituteVar ([‖⇴]-of-varShift𝐒 px) py) ([‖⇴]-of-substituteVar px pz))
-- [‖⇴]-of-substituteVar {n = bound-𝐒(n)} ([‖⇴]-of-varShift𝐒 {n = n} px) py
-- _‖⇴_.β ([‖⇴]-of-substituteVar {n = 𝐒 n} ([‖⇴]-of-varShift𝐒 {n = n} px) ([‖⇴]-of-varShift𝐒 {n = 𝐒 n} pyᵣ)) ([‖⇴]-of-substituteVar px pyᵣ)
-- β ([‖⇴]-of-substituteVar ([‖⇴]-of-varShift𝐒 px) pyₗ) ([‖⇴]-of-substituteVar px pyᵣ)

[‖⇴]-diamondProperty : ∀ₗ(Names.DiamondProperty(_‖⇴_ {d}))
[‖⇴]-diamondProperty var var = [∃]-intro _ ⦃ [∧]-intro var var ⦄
[‖⇴]-diamondProperty (apply l₁ l₂) (apply r₁ r₂) =
  let [∃]-intro f ⦃ [∧]-intro f₁ f₂ ⦄ = [‖⇴]-diamondProperty l₁ r₁
      [∃]-intro x ⦃ [∧]-intro x₁ x₂ ⦄ = [‖⇴]-diamondProperty l₂ r₂
  in  [∃]-intro (Apply f x) ⦃ [∧]-intro (apply f₁ x₁) (apply f₂ x₂) ⦄
[‖⇴]-diamondProperty (abstr p) (abstr q) =
  let [∃]-intro f ⦃ [∧]-intro f₁ f₂ ⦄ = [‖⇴]-diamondProperty p q
  in  [∃]-intro (Abstract f) ⦃ [∧]-intro (abstr f₁) (abstr f₂) ⦄
[‖⇴]-diamondProperty (β l₁ l₂) (β r₁ r₂) =
  let [∃]-intro f ⦃ [∧]-intro f₁ f₂ ⦄ = [‖⇴]-diamondProperty l₁ r₁
      [∃]-intro x ⦃ [∧]-intro x₁ x₂ ⦄ = [‖⇴]-diamondProperty l₂ r₂
  in [∃]-intro (substituteVar maximum x f) ⦃ [∧]-intro ([‖⇴]-of-substituteVar x₁ f₁) ([‖⇴]-of-substituteVar x₂ f₂) ⦄
[‖⇴]-diamondProperty (apply(abstr l₁) l₂) (β r₁ r₂) =
  let [∃]-intro f ⦃ [∧]-intro f₁ f₂ ⦄ = [‖⇴]-diamondProperty l₁ r₁
      [∃]-intro x ⦃ [∧]-intro x₁ x₂ ⦄ = [‖⇴]-diamondProperty l₂ r₂
  in  [∃]-intro (substituteVar maximum x f) ⦃ [∧]-intro (β f₁ x₁) ([‖⇴]-of-substituteVar x₂ f₂) ⦄
[‖⇴]-diamondProperty (β l₁ l₂) (apply (abstr r₁) r₂) =
  let [∃]-intro f ⦃ [∧]-intro f₁ f₂ ⦄ = [‖⇴]-diamondProperty l₁ r₁
      [∃]-intro x ⦃ [∧]-intro x₁ x₂ ⦄ = [‖⇴]-diamondProperty l₂ r₂
  in  [∃]-intro (substituteVar maximum x f) ⦃ [∧]-intro ([‖⇴]-of-substituteVar x₁ f₁) (β f₂ x₂) ⦄

[‖⇴]-confluence : Names.Confluence(_‖⇴_ {d})
[‖⇴]-confluence = DiamondPropertyProofs.confluence(_‖⇴_) [‖⇴]-diamondProperty

open import Structure.Relator.Properties

[‖⇴*][β⇴*]-equivalence : (x ‖⇴* y) ↔ (x β⇴* y)
[‖⇴*][β⇴*]-equivalence = [↔]-intro l* r* where
  l : (x β⇴ y) → (x ‖⇴ y)
  l β = β [‖⇴]-reflexivity-raw [‖⇴]-reflexivity-raw
  l (cong-applyₗ p) = apply (l p) [‖⇴]-reflexivity-raw
  l (cong-applyᵣ p) = apply [‖⇴]-reflexivity-raw (l p)

  l* : (x β⇴* y) → (x ‖⇴* y)
  l* at = at
  l* (prepend x p) = prepend(l x) (l* p)

  -- Termination: OK because substituteVar should not make the term "bigger" in some sense.
  r : (x ‖⇴ y) → (x β⇴* y)
  r var = reflexivity(_β⇴*_)
  r (apply pf px) = compatible₁(_β⇴*_)(_β⇴*_)(\f → Apply f _) (r pf) 🝖 compatible₁(_β⇴*_)(_β⇴*_)(\x → Apply _ x) (r px)
  r (abstr pb) = {!compatible₁(_β⇴*_)(_β⇴*_)(Abstract) ?!} -- TODO: This result should be about (_⇴_), not (_β⇴_), but also without η.
  r (β p1 p2) = prepend β (r([‖⇴]-of-substituteVar p2 p1))

  r* : (x ‖⇴* y) → (x β⇴* y)
  r* at = at
  r* (prepend x p) =  r x 🝖 r* p

module _
  {ℓ₁ ℓ₂ ℓₗ₁ ℓₗ₂}
  {A : Type{ℓₗ₁}}
  {B : Type{ℓₗ₂}}
  {_→₁_ : A → A → Type{ℓ₁}}
  {_→₂_ : B → B → Type{ℓ₂}}
  (f : A → B)
  where

  CommonReduct-map : (∀{a b} → (Walk(_→₁_) a b) → (Walk(_→₂_) (f(a)) (f(b)))) → (∀{w a b} → CommonReduct(_→₁_) w a b → CommonReduct(_→₂_) (f(w)) (f(a)) (f(b)))
  CommonReduct-map F* ([∧]-intro aw bw) = [∧]-intro (F* aw) (F* bw)

  Joinable-map : (∀{a b} → (Walk(_→₁_) a b) → (Walk(_→₂_) (f(a)) (f(b)))) → (∀{a b} → Joinable(_→₁_) a b → Joinable(_→₂_) (f(a)) (f(b)))
  Joinable-map F* ([∃]-intro w ⦃ p ⦄) = [∃]-intro (f(w)) ⦃ CommonReduct-map F* p ⦄

-- Also called: Church-Rosser's theorem.
[β⇴]-confluence : Names.Confluence(_β⇴_ {d})
[β⇴]-confluence ab ac = Joinable-map
  Functional.id
  ([↔]-to-[→] [‖⇴*][β⇴*]-equivalence)
  ([‖⇴]-confluence ([↔]-to-[←] [‖⇴*][β⇴*]-equivalence ab) ([↔]-to-[←] [‖⇴*][β⇴*]-equivalence ac))
