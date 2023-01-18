module Miscellaneous.Ordinal where

open import Functional
open import Logic.Predicate
import      Lvl
open import Numeral.Natural
import      Numeral.Natural.Relation.Order as ℕ
open import Syntax.Function
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable f : A → B
private variable _▫_ _▫₁_ _▫₂_ _▫₃_ : A → B → C
private variable i n x y : T

Increasing : (A → A → Type{ℓ₁}) → (B → B → Type{ℓ₂}) → (A → B) → Type
Increasing(_<₁_)(_<₂_)(f) = ∀{x y} → (x <₁ y) → (f(x) <₂ f(y))
-- ∀²(pointwise₂,₂(_→ᶠ_)(_<₁_)((_<₂_) on₂ f))

Increasing₂ : (A → A → Type{ℓ₁}) → (B → B → Type{ℓ₂}) → (C → C → Type{ℓ₃}) → (A → B → C) → Type
Increasing₂(_<₁_)(_<₂_)(_<₃_)(f) = ∀{x₁ y₁}{x₂ y₂} → (x₁ <₁ y₁) → (x₂ <₂ y₂) → (f x₁ x₂ <₃ f y₁ y₂)

-- TODO: Is it possible to express that (_⋅_) defined below is order-isomorphic to (_⨯_) of two ordinals using this?
-- OrderHomomorphism : (A → A → Type{ℓ₁}) → (B → B → Type{ℓ₂}) → (A → B) → Type
-- OrderHomomorphism(_<₁_)(_<₂_)(f) = ∀²(pointwise₂,₂(_↔_)(_<₁_)((_<₂_) on₂ f))

-- TODO: Not all ordinals. Maybe impossible to express a type of all ordinals? Is this a problem when using types https://en.wikipedia.org/wiki/Burali-Forti_paradox ?
data Ordinal : Type{Lvl.𝟎}
data _≤_ : Ordinal → Ordinal → Type{Lvl.𝟎}
_<_ : Ordinal → Ordinal → Type{Lvl.𝟎}

data Ordinal where
  𝟎   : Ordinal
  𝐒   : Ordinal → Ordinal
  lim : (f : ℕ → Ordinal) → (Increasing(ℕ._<_)(_<_)(f)) → Ordinal

pattern 𝟏 = 𝐒(𝟎)

x < y = 𝐒(x) ≤ y

data _≤_ where
  minimal  : ∀{x} → (𝟎 ≤ x)
  step     : ∀{x y} → (x ≤ y) → (𝐒(x) ≤ 𝐒(y))
  maximal  : ∀{f}{p : Increasing(ℕ._<_)(_<_)(f)}{x}{i} → (x ≤ f(i)) → (x < lim f p)
  supremum : ∀{f}{p : Increasing(ℕ._<_)(_<_)(f)}{x} → (∀{i} → (f(i) < x)) → (lim f p ≤ x)

open import Logic.Propositional

_≥_ = swap(_≤_)
_>_ = swap(_<_)

_≡_ : Ordinal → Ordinal → Type
x ≡ y = (x ≥ y) ∧ (x ≤ y)

[≤]-unstep : ∀{x y} → (𝐒(x) ≤ 𝐒(y)) → (x ≤ y)
[≤]-unstep (step xy) = xy

[<]-minimal : 𝟎 < 𝐒(x)
[<]-minimal = step minimal

𝐒-increasing : Increasing(_<_)(_<_) 𝐒
𝐒-increasing = step

module _
  {ℓ}
  (P : Ordinal → Type{ℓ})
  (p0 : P(𝟎))
  (ps : ∀{x} → P(x) → P(𝐒(x)))
  (pl : ∀{f}{p : Increasing(ℕ._<_)(_<_)(f)} → (∀{i} → P(f(i))) → P(lim f p))
  where

  elim : ((x : Ordinal) → P(x))
  elim 𝟎 = p0
  elim (𝐒(x)) = ps(elim x)
  elim (lim f p) = pl \{i} → elim(f(i))

module _
  {ℓ}
  (P : ∀{x y} → (ord : x ≤ y) → Type{ℓ})
  (pmin  : ∀{x} → P(minimal{x}))
  (pstep : ∀{x y}{ord : x ≤ y} → P(ord) → P(step ord))
  (pmax  : ∀{f}{p : Increasing(ℕ._<_)(_<_)(f)}{x}{i}{ord : x ≤ f(i)} → P(ord) → P(maximal{f}{p}{x}{i} ord))
  (psup  : ∀{f}{p : Increasing(ℕ._<_)(_<_)(f)}{x}{ord : ∀{i} → (f(i) < x)} → (∀{i} → P(ord{i})) → P(supremum{f}{p}{x} ord))
  where

  [≤]-elim : (∀{x y} → (ord : x ≤ y) → P(ord))
  [≤]-elim minimal        = pmin
  [≤]-elim (step ord)     = pstep([≤]-elim ord)
  [≤]-elim (maximal ord)  = pmax([≤]-elim ord)
  [≤]-elim (supremum ord) = psup([≤]-elim ord)

module _
  {ℓ}
  (P : ∀{x y} → (ord : x < y) → Type{ℓ})
  (pmin  : ∀{x} → P([<]-minimal{x}))
  (pstep : ∀{x y}{ord : x < y} → P(ord) → P(𝐒-increasing ord))
  (pmax  : ∀{f}{p : Increasing(ℕ._<_)(_<_)(f)}{x}{i}{ord : 𝐒(x) ≤ 𝐒(f(i))} → P(ord) → P(maximal {f}{p}{x}{i} ([≤]-unstep ord)))
  (psup  : ∀{f}{p : Increasing(ℕ._<_)(_<_)(f)}{x}{ord : ∀{i} → (f(i) < x)} → (∀{i} → P(ord{i})) → P(step(supremum {f}{p}{x} ord)))
  where

  [<]-elim : (∀{x y} → (ord : x < y) → P(ord))
  [<]-elim {𝟎}       (step minimal)          = pmin
  [<]-elim {𝐒 x}     (step ord)              = pstep([<]-elim ord)
  [<]-elim {lim f x} (step(supremum ord))    = psup([<]-elim ord)
  [<]-elim {𝟎}       (maximal minimal)       = pmax pmin
  [<]-elim {𝐒 x}     (maximal ord)           = pmax(pstep([<]-elim ord))
  [<]-elim {lim f x} (maximal(supremum ord)) = pmax(psup([<]-elim ord))

import      Structure.Relator.Names as Names
open import Structure.Relator.Properties

instance
  [≤]-reflexivity : Reflexivity(_≤_)
  [≤]-reflexivity = intro proof where
    proof : Names.Reflexivity(_≤_)
    proof {𝟎}       = minimal
    proof {𝐒 x}     = step proof
    proof {lim f x} = supremum(maximal proof)

instance
  [≤]-transitivity : Transitivity(_≤_)
  [≤]-transitivity = intro proof where
    proof : Names.Transitivity(_≤_)
    proof minimal       _             = minimal
    proof (supremum xy) yz            = supremum (proof xy yz)
    proof (maximal xy)  (supremum yz) = proof (step xy) yz
    proof (step xy)     (step yz)     = step (proof xy yz)
    proof (step xy)     (maximal yz)  = maximal (proof xy yz)

instance
  [<][≤]-sub : (_<_) ⊆₂ (_≤_)
  [<][≤]-sub = intro proof where
    proof : Names.Sub₂(_<_)(_≤_)
    proof {𝟎}       {_}       _             = minimal
    proof {𝐒 x}     {𝐒 y}     (step ord)    = step(proof ord)
    proof {𝐒 x}     {lim g q} (maximal ord) = maximal(proof ord)
    proof {lim f p} {𝐒 y}     (step ord)    = supremum(step(transitivity(_≤_) (proof(maximal(reflexivity(_≤_)))) ord))
    proof {lim f p} {lim g q} (maximal ord) = supremum(maximal(transitivity(_≤_) (proof(maximal(reflexivity(_≤_)))) ord))

instance
  [<]-irreflexivity : Irreflexivity(_<_)
  [<]-irreflexivity = intro proof where
    proof : Names.Irreflexivity(_<_)
    proof (step p)              = proof p
    proof (maximal(supremum x)) = proof x

open import Structure.Relator.Properties.Proofs

instance
  [≡][≥]-sub : (_≡_) ⊆₂ (_≥_)
  [≡][≥]-sub = intro [∧]-elimₗ

instance
  [≡][≤]-sub : (_≡_) ⊆₂ (_≤_)
  [≡][≤]-sub = intro [∧]-elimᵣ

instance
  [≤][≡]-subtransitivityₗ : Subtransitivityₗ(_≤_)(_≡_)
  [≤][≡]-subtransitivityₗ = subrelation-transitivity-to-subtransitivityₗ

instance
  [≤][≡]-subtransitivityᵣ : Subtransitivityᵣ(_≤_)(_≡_)
  [≤][≡]-subtransitivityᵣ = subrelation-transitivity-to-subtransitivityᵣ

instance
  [≤][<]-subtransitivityₗ : Subtransitivityₗ(_≤_)(_<_)
  [≤][<]-subtransitivityₗ = subrelation-transitivity-to-subtransitivityₗ

instance
  [≤][<]-subtransitivityᵣ : Subtransitivityᵣ(_≤_)(_<_)
  [≤][<]-subtransitivityᵣ = subrelation-transitivity-to-subtransitivityᵣ

instance
  [<][≤]-subtransitivityᵣ : Subtransitivityᵣ(_<_)(_≤_)
  [<][≤]-subtransitivityᵣ = intro proof where
    proof : Names.Subtransitivityᵣ(_<_)(_≤_)
    proof (step minimal)      (step yz)              = step minimal
    proof (step minimal)      (maximal{i = i} yz)    = maximal{i = i} minimal
    proof (step(step xy))     (step yz)              = step(proof(step xy) yz)
    proof (step(step xy))     (maximal yz)           = maximal(proof(step xy) yz)
    proof (step(maximal xy))  (step(supremum yz))    = step(proof(step xy) yz)
    proof (step(maximal xy))  (maximal(supremum yz)) = maximal(proof(step xy) yz)
    proof (step(supremum xy)) (step yz)              = step(supremum(proof xy yz))
    proof (step(supremum xy)) (maximal yz)           = maximal(supremum(proof xy yz))
    proof (maximal xy)        (supremum yz)          = proof(step xy) yz

instance
  [<][≤]-subtransitivityₗ : Subtransitivityₗ(_<_)(_≤_)
  [<][≤]-subtransitivityₗ = intro proof where
    proof : Names.Subtransitivityₗ(_<_)(_≤_)
    proof                             minimal       (step yz)                     = step minimal
    proof                             minimal       (maximal{i = i} yz)           = maximal{i = i} minimal
    proof                             (step xy)     (step yz)                     = step(proof xy yz)
    proof                             (step xy)     (maximal yz)                  = maximal(proof xy yz)
    proof {𝐒 x} {lim y py} {𝐒 z}      (maximal xy)  (step(supremum yz))           = step(proof xy yz)
    proof {𝐒 x} {lim y py} {lim z pz} (maximal xy)  (maximal{i = i}(supremum yz)) = maximal{i = i} (proof xy yz)
    proof                             (supremum xy) (step yz)                     = step(supremum(subtransitivityᵣ(_<_)(_≤_) xy yz))
    proof                             (supremum xy) (maximal{i = i} yz)           = maximal{i = i} (supremum(subtransitivityᵣ(_<_)(_≤_) xy yz))

instance
  [<][≡]-subtransitivityₗ : Subtransitivityₗ(_<_)(_≡_)
  [<][≡]-subtransitivityₗ = subrelation-subtransitivityₗ-to-subtransitivityₗ {_▫₁_ = _≡_}{_▫₂_ = _≤_}

instance
  [<][≡]-subtransitivityᵣ : Subtransitivityᵣ(_<_)(_≡_)
  [<][≡]-subtransitivityᵣ = subrelation-subtransitivityᵣ-to-subtransitivityᵣ {_▫₁_ = _≡_}{_▫₂_ = _≤_}

instance
  [<]-transitivity : Transitivity(_<_)
  [<]-transitivity = intro(subtransitivityᵣ(_≤_)(_<_))

instance
  [<]-asymmetry : Asymmetry(_<_)
  [<]-asymmetry = intro(irreflexivity(_<_) ∘₂ transitivity(_<_))

[≤][>]-contradiction : (x ≤ y) → (x > y) → ⊥
[≤][>]-contradiction = irreflexivity(_<_) ∘₂ subtransitivityₗ(_<_)(_≤_)

[<]-of-𝐒 : x < 𝐒(x)
[<]-of-𝐒 = step(reflexivity(_≤_))

[≤]-of-𝐒 : x ≤ 𝐒(x)
[≤]-of-𝐒 = sub₂(_<_)(_≤_) [<]-of-𝐒

[<]-minimum-lim : ∀{p : Increasing(ℕ._<_)(_<_)(f)} → (𝟎 < lim f p)
[<]-minimum-lim = maximal{i = 𝟎} minimal

[<]-limit : ∀{p : Increasing(ℕ._<_)(_<_)(f)} → (f(i) < lim f p)
[<]-limit = maximal(reflexivity(_≤_))

import Numeral.Natural.Relation.Order.Proofs as ℕ

𝐒-[ℕ≤][≤]-preserving-when-increasing : Increasing(ℕ._<_)(_<_)(f) → (𝐒(f(i)) ≤ f(𝐒(i)))
𝐒-[ℕ≤][≤]-preserving-when-increasing inc = inc(reflexivity(ℕ._≤_))
-- 𝐒-[ℕ≤][≤]-preserving-when-increasing {i = 𝟎}   inc = inc(ℕ.succ ℕ.min)
-- 𝐒-[ℕ≤][≤]-preserving-when-increasing {i = 𝐒 i} inc = 𝐒-[ℕ≤][≤]-preserving-when-increasing(inc ∘ ℕ.succ)

𝐒-[≤]-preserving-when-increasing : Increasing(_<_)(_<_)(f) → (𝐒(f(i)) ≤ f(𝐒(i)))
𝐒-[≤]-preserving-when-increasing inc = inc(reflexivity(_≤_))
-- 𝐒-[≤]-preserving-when-increasing {i = 𝟎}       inc = inc(step minimal)
-- 𝐒-[≤]-preserving-when-increasing {i = 𝐒 i}     inc = inc(step(𝐒-[≤]-preserving-when-increasing id))
-- 𝐒-[≤]-preserving-when-increasing {i = lim f p} inc = inc(step(supremum(\{i} → maximal{i = i} (reflexivity(_≤_)))))

instance
  [≡]-reflexivity : Reflexivity(_≡_)
  [≡]-reflexivity = intro([∧]-intro (reflexivity(_≤_)) (reflexivity(_≤_)))

open import Logic.Propositional.Theorems

instance
  [≡]-symmetry : Symmetry(_≡_)
  [≡]-symmetry = intro [∧]-symmetry

instance
  [≡]-transitivity : Transitivity(_≡_)
  [≡]-transitivity = intro \([∧]-intro xyₗ xyᵣ) ([∧]-intro yzₗ yzᵣ) → [∧]-intro (transitivity(_≤_) yzₗ xyₗ) (transitivity(_≤_) xyᵣ yzᵣ)

open import Structure.Relator.Equivalence
open import Structure.Setoid using (Equiv ; intro)

instance
  Ordinal-equiv : Equiv(Ordinal)
  Ordinal-equiv = intro(_≡_) ⦃ intro ⦄

open import Structure.Function

instance
  𝐒-function : Function(𝐒)
  𝐒-function = intro \([∧]-intro xyₗ xyᵣ) → [∧]-intro (step xyₗ) (step xyᵣ)

open import Structure.Function.Domain
import      Structure.Function.Names as Names

instance
  𝐒-injective : Injective(𝐒)
  𝐒-injective = intro proof where
    proof : Names.Injective(𝐒)
    proof ([∧]-intro (step xyₗ) (step xyᵣ)) = [∧]-intro xyₗ xyᵣ

open import Structure.Relator.Ordering
open        Structure.Relator.Ordering.Strict.Properties using (intro)

instance
  Ordinal-wellFounded : Strict.Properties.WellFounded(_<_)
  Ordinal-wellFounded {n} = intro ⦃ proof{n} ⦄ where
    proof : ∀{y x} → ⦃ _ : (x < y) ⦄ → Strict.Properties.Accessibleₗ(_<_)(x)
    proof {_}          {𝟎}                      = intro ⦃ \ ⦃ ⦄ ⦄
    proof {𝐒 x}        {𝐒 y}     ⦃ step xy ⦄    = intro ⦃ \{ ⦃ step zx ⦄ → Strict.Properties.Accessibleₗ.proof Ordinal-wellFounded ⦃ subtransitivityₗ(_<_)(_≤_) zx xy ⦄ } ⦄
    proof {.(lim _ _)} {𝐒 y}     ⦃ maximal xy ⦄ = intro ⦃ \{ ⦃ step zx ⦄ → Strict.Properties.Accessibleₗ.proof Ordinal-wellFounded ⦃ subtransitivityₗ(_<_)(_≤_) zx xy ⦄ } ⦄
    proof {.(𝐒 _)}     {lim f p} ⦃ step(supremum xy) ⦄ = intro ⦃ \{ ⦃ maximal zx ⦄ → Strict.Properties.Accessibleₗ.proof Ordinal-wellFounded ⦃ subtransitivityₗ(_<_)(_≤_) zx xy ⦄ } ⦄
    proof {.(lim _ _)} {lim f p} ⦃ maximal(supremum xy) ⦄ = intro ⦃ \{ ⦃ maximal zx ⦄ → Strict.Properties.Accessibleₗ.proof Ordinal-wellFounded ⦃ subtransitivityₗ(_<_)(_≤_) zx xy ⦄ } ⦄

open import Data
open import Numeral.Natural
open import Numeral.Natural.Induction
open import Syntax.Number

instance
  Ordinal-numeral : InfiniteNumeral(Ordinal)
  Ordinal-numeral = record { num = \n ⦃ _ ⦄ → ℕ-elim(const Ordinal) 𝟎 (const 𝐒) n }

open import Type.Identity
open import Type.Identity.Proofs

instance
  Ordinal-num-injective : Injective ⦃ Id-equiv ⦄ (InfiniteNumeral.num{T = Ordinal})
  Ordinal-num-injective = intro(\{x}{y} → proof{x}{y}) where
    proof : Names.Injective ⦃ Id-equiv ⦄ InfiniteNumeral.num
    proof{𝟎}  {𝟎}   xy = intro
    proof{𝐒 x}{𝐒 y} xy = congruence₁(𝐒) (proof{x}{y} (injective(𝐒) xy)) where
      instance _ = Id-equiv
      instance _ = Id-to-function

ω : Ordinal
ω = lim InfiniteNumeral.num p where
  p : Increasing(ℕ._<_)(_<_)(InfiniteNumeral.num)
  p {𝟎}    {𝐒 i₂} (ℕ.succ ord) = step minimal
  p {𝐒 i₁} {𝐒 i₂} (ℕ.succ ord) = step(p ord)

{-
ω2 : Ordinal
ω2 = lim (𝐒 ∘ 𝐒) (step ∘ step)

test : ω < ω2
test = maximal{i = ω} {!!}
-}

[≤]-of-ω : num(n) < ω
[≤]-of-ω {n} = [<]-limit {i = n}

open import Syntax.Transitivity

[<]-num-lim : ∀{f}{p : Increasing(ℕ._<_)(_<_)(f)} → (num(n) < lim f p)
[<]-num-lim{𝟎} = [<]-minimum-lim
[<]-num-lim{𝐒 n}{f}{p} with [<]-num-lim{n}{f}{p}
... | maximal{i = i} ord = maximal{i = 𝐒 i} $
  𝐒(num n) 🝖[ _≤_ ]-[ step ord ]
  𝐒(f(i))  🝖[ _≤_ ]-[ 𝐒-[ℕ≤][≤]-preserving-when-increasing p ]
  f(𝐒(i))  🝖-end

[≤]-increasing-function-num-min : ∀{p : Increasing(ℕ._<_)(_<_)(f)} → (num(i) ≤ f(i))
[≤]-increasing-function-num-min {f} {𝟎}   {p} = minimal
[≤]-increasing-function-num-min {f} {𝐒 i} {p} =
  𝐒(num(i)) 🝖[ _≤_ ]-[ step ([≤]-increasing-function-num-min {f}{i}{p}) ]
  𝐒(f(i))   🝖[ _≤_ ]-[ 𝐒-[ℕ≤][≤]-preserving-when-increasing p ]
  f(𝐒(i))   🝖-end

ω-minimal-lim : ∀{f}{p : Increasing(ℕ._<_)(_<_)(f)} → (ω ≤ lim f p)
ω-minimal-lim{f}{p} = supremum \{n} → [<]-num-lim {n}

Increasing-compose : {f : B → C}{g : A → B} → Increasing(_▫₂_)(_▫₃_)(f) → Increasing(_▫₁_)(_▫₂_)(g) → Increasing(_▫₁_)(_▫₃_)(f ∘ g)
Increasing-compose inc-f inc-g = inc-f ∘ inc-g

-- [<]-stepᵣ : (x < y) → (x < 𝐒(y))
-- [≤]-stepᵣ : (x ≤ y) → (x ≤ 𝐒(y))

Increasing-relation : ∀{f}{g} → (∀{x} → f(x) ≡ g(x)) → Increasing(ℕ._<_)(_<_)(f) → Increasing(ℕ._<_)(_<_)(g)
Increasing-relation {f}{g} fg inc-f {x}{y} xy =
  g(x) 🝖[ _≡_ ]-[ symmetry(_≡_) fg ]-sub
  f(x) 🝖[ _<_ ]-[ inc-f xy ]-super
  f(y) 🝖[ _≡_ ]-[ fg ]
  g(y) 🝖[ _≡_ ]-end

lim-[≤]-general-compatible : ∀{f}{pf : Increasing(ℕ._<_)(_<_)(f)}{g}{pg : Increasing(ℕ._<_)(_<_)(g)}{h : ℕ → ℕ} → (∀{x} → f(x) ≤ g(h(x))) → (lim f pf ≤ lim g pg)
lim-[≤]-general-compatible {h = h} fg = supremum(\{i} → maximal{i = h(i)} (fg{i}))

lim-general-function : ∀{f}{pf : Increasing(ℕ._<_)(_<_)(f)}{g}{pg : Increasing(ℕ._<_)(_<_)(g)}{l r : ℕ → ℕ} → (∀{x} → f(l(x)) ≡ g(x)) → (∀{x} → f(x) ≡ g(r(x))) → (lim f pf ≡ lim g pg)
lim-general-function {l = l}{r = r} fgl fgr = [∧]-intro
  (lim-[≤]-general-compatible(\{x} → sub₂(_≡_)(_≥_) (fgl{x})))
  (lim-[≤]-general-compatible(\{x} → sub₂(_≡_)(_≤_) (fgr{x})))

lim-[≤]-compatible : ∀{f}{pf : Increasing(ℕ._<_)(_<_)(f)}{g}{pg : Increasing(ℕ._<_)(_<_)(g)} → (∀{x} → f(x) ≤ g(x)) → (lim f pf ≤ lim g pg)
lim-[≤]-compatible = lim-[≤]-general-compatible

lim-function : ∀{f}{pf : Increasing(ℕ._<_)(_<_)(f)}{g}{pg : Increasing(ℕ._<_)(_<_)(g)} → (fg : ∀{x} → f(x) ≡ g(x)) → (lim f pf ≡ lim g pg)
lim-function fg = lim-general-function fg fg

lim-function-default : ∀{f}{pf : Increasing(ℕ._<_)(_<_)(f)}{g} → (fg : ∀{x} → f(x) ≡ g(x)) → (lim f pf ≡ lim g (Increasing-relation fg pf))
lim-function-default{f}{pf}{g} fg = lim-function{f}{pf}{g}{_} fg

open import Structure.Operator.Properties
import      Structure.Operator.Names as Names

_+_ : Ordinal → Ordinal → Ordinal
[+]ₗ-order : ∀{a b} → (a ≤ (a + b))
[+]ᵣ-weaklyIncreasing : Increasing(_≤_)(_≤_)(x +_)
[+]ᵣ-increasing : Increasing(_<_)(_<_)(x +_)

x + 𝟎       = x
x + 𝐒(y)    = 𝐒(x + y)
x + lim f p = lim(y ↦ (x + f(y))) ([+]ᵣ-increasing ∘ p)

[+]ₗ-order {a}{𝟎}       = reflexivity(_≤_)
[+]ₗ-order {a}{𝐒 b}     = [+]ₗ-order{a}{b} 🝖 [≤]-of-𝐒
[+]ₗ-order {a}{lim f x} = sub₂(_<_)(_≤_) (maximal{i = 𝟎} ([+]ₗ-order{a}{f(𝟎)}))

[+]ᵣ-weaklyIncreasing minimal              = [+]ₗ-order
[+]ᵣ-weaklyIncreasing (step ord)           = step([+]ᵣ-weaklyIncreasing ord)
[+]ᵣ-weaklyIncreasing (maximal{i = i} ord) = maximal{i = i} ([+]ᵣ-weaklyIncreasing ord)
[+]ᵣ-weaklyIncreasing (supremum ord)       = supremum([+]ᵣ-weaklyIncreasing ord)

[+]ᵣ-increasing (step ord)    = step([+]ᵣ-weaklyIncreasing ord)
[+]ᵣ-increasing (maximal ord) = maximal([+]ᵣ-weaklyIncreasing ord)

[+]ₗ-weaklyIncreasing : Increasing(_≤_)(_≤_)(_+ y)
[+]ₗ-weaklyIncreasing {𝟎}       ord = ord
[+]ₗ-weaklyIncreasing {𝐒 a}     ord = step ([+]ₗ-weaklyIncreasing {a} ord)
[+]ₗ-weaklyIncreasing {lim f p} ord = lim-[≤]-compatible \{x} → [+]ₗ-weaklyIncreasing {f(x)} ord

[+]-weaklyIncreasing : Increasing₂(_≤_)(_≤_)(_≤_)(_+_)
[+]-weaklyIncreasing {x₁} {y₁} {x₂} {y₂} p1 p2 = [+]ₗ-weaklyIncreasing p1 🝖 [+]ᵣ-weaklyIncreasing p2

instance
  [+]-identityᵣ : Identityᵣ(_+_)(𝟎)
  [+]-identityᵣ = intro(reflexivity(_≡_))

instance
  [+]-identityₗ : Identityₗ(_+_)(𝟎)
  [+]-identityₗ = intro proof where
    proof : Names.Identityₗ(_+_)(𝟎)
    proof {𝟎} =
      𝟎 + 𝟎 🝖[ _≡_ ]-[]
      𝟎     🝖-end
    proof {𝐒 x} =
      (𝟎 + 𝐒(x)) 🝖[ _≡_ ]-[]
      𝐒(𝟎 + x)   🝖[ _≡_ ]-[ congruence₁(𝐒) (proof{x}) ]
      𝐒(x)       🝖-end
    proof {lim f p} =
      (𝟎 + lim f p)        🝖[ _≡_ ]-[]
      lim(\y → 𝟎 + f(y)) _ 🝖[ _≡_ ]-[ lim-function(\{x} → proof{f(x)}) ]
      lim f p              🝖-end

open import Structure.Operator

instance
  [+]-function : BinaryOperator(_+_)
  [+]-function = BinaryOperator-unary-intro(_+_) (intro left) (intro right) where
    left : Names.Congruence₁(_+ y)
    left{𝟎}       xy = xy
    left{𝐒 y}     xy = congruence₁(𝐒) (left{y} xy)
    left{lim f p} xy = lim-function \{x} → left{f(x)} xy

    right : Names.Congruence₁(x +_)
    right xy = [∧]-intro
      ([+]ᵣ-weaklyIncreasing (sub₂(_≡_)(_≥_) xy))
      ([+]ᵣ-weaklyIncreasing (sub₂(_≡_)(_≤_) xy))

instance
  [+]-associativity : Associativity(_+_)
  [+]-associativity = intro(\{x}{y}{z} → proof{x}{y}{z}) where
    proof : Names.Associativity(_+_)
    proof{x}{y}{𝟎}       = reflexivity(_≡_)
    proof{x}{y}{𝐒 z}     = congruence₁(𝐒) (proof{x}{y}{z})
    proof{x}{y}{lim f p} = lim-function \{a} → proof{x}{y}{f(a)}

[+]ᵣ-order : ∀{a b} → (b ≤ (a + b))
[+]ᵣ-order {a} {𝟎}       = minimal
[+]ᵣ-order {a} {𝐒 b}     = step([+]ᵣ-order {a}{b})
[+]ᵣ-order {a} {lim f p} = lim-[≤]-compatible \{x} → [+]ᵣ-order {a}{f(x)}

import      Numeral.Natural.Oper as ℕ
import      Numeral.Natural.Oper.Proofs.Rewrite as ℕ
open import Structure.Function.Multi

instance
  num-preserves-[+] : Preserving₂ InfiniteNumeral.num (ℕ._+_)(_+_)
  num-preserves-[+] = intro(\{x}{y} → proof{x}{y}) where
    proof : Names.Preserving₂ InfiniteNumeral.num (ℕ._+_)(_+_)
    proof {x}{𝟎}   = reflexivity(_≡_)
    proof {x}{𝐒 y} = congruence₁(𝐒) (proof {x}{y})

[+]ᵣ-of-ℕ-ω-is-identity : (num(n) + ω) ≡ ω
[+]ᵣ-of-ℕ-ω-is-identity{n} = [∧]-intro [+]ᵣ-order (lt{n}) where
  lt : (num(x) + ω) ≤ ω
  lt{x} =
    num(x) + ω                  🝖[ _≤_ ]-[]
    lim(\y → num(x) + num(y)) _ 🝖[ _≡_ ]-[ lim-function-default(\{y} → symmetry(_≡_) (preserving₂ InfiniteNumeral.num (ℕ._+_)(_+_) {x}{y})) ]-sub
    lim(\y → num(x ℕ.+ y)) _    🝖[ _≤_ ]-[ lim-[≤]-general-compatible{h = x ℕ.+_} (reflexivity(_≤_)) ]
    lim(\y → num(y)) _          🝖[ _≤_ ]-[]
    ω 🝖-end

[≤][>]-disjoint : (x ≤ y) → (x > y) → ⊥
[≤][>]-disjoint (step le)     (step gt)           = [≤][>]-disjoint le gt
[≤][>]-disjoint (maximal le)  (step(supremum gt)) = [≤][>]-disjoint le gt
[≤][>]-disjoint (supremum le) (maximal gt)        = [≤][>]-disjoint gt le

[+]-noncommutative : ¬ Commutativity(_+_)
[+]-noncommutative com = let instance _ = com in [≤][>]-disjoint
  (sub₂(_≡_)(_≤_) $
    𝐒(ω)    🝖[ _≡_ ]-[]
    (ω + 𝟏) 🝖[ _≡_ ]-[ commutativity(_+_) {ω}{𝟏} ]
    (𝟏 + ω) 🝖[ _≡_ ]-[ [+]ᵣ-of-ℕ-ω-is-identity {𝟏} ]
    ω       🝖-end
  )
  [<]-of-𝐒

[+]ₗ-increasing : Increasing(_<_)(_≤_)(_+ y)
[+]ₗ-increasing {𝟎}      {x}{y} ord = sub₂(_<_)(_≤_) ord
[+]ₗ-increasing {𝐒 a}    {x}{y} ord = step([+]ₗ-increasing ord)
[+]ₗ-increasing {lim f p}{x}{y} ord = supremum \{i} → maximal{i = i} ([+]ₗ-increasing ord)

[+]ₗ-strict-order : (y > 𝟎) → (x < (x + y))
[+]ₗ-strict-order {𝐒 y}     {x} pos = step [+]ₗ-order
[+]ₗ-strict-order {lim f p} {x} pos = maximal{i = 𝟎} [+]ₗ-order

{-
[≤]-or-[>] : (x ≤ y) ∨ (x > y)
[≤]-or-[>] {𝟎}       {_}       = [∨]-introₗ minimal
[≤]-or-[>] {𝐒 x}     {𝟎}       = [∨]-introᵣ (step minimal)
[≤]-or-[>] {𝐒 x}     {𝐒 y}     = [∨]-elim2 step step ([≤]-or-[>] {x}{y})
[≤]-or-[>] {𝐒 x}     {lim g q} = {!!}
[≤]-or-[>] {lim f p} {𝟎}       = [∨]-introᵣ [<]-minimum-lim
[≤]-or-[>] {lim f p} {𝐒 y}     = {!!}
[≤]-or-[>] {lim f p} {lim g q} = {!!}

[≤]-to-[<][≡] : (x ≤ y) → (x < y) ∨ (x ≡ y)
[≤]-to-[<][≡] {y = 𝟎}       minimal = [∨]-introᵣ (reflexivity(_≡_))
[≤]-to-[<][≡] {y = 𝐒 _}     minimal = [∨]-introₗ [<]-minimal
[≤]-to-[<][≡] {y = lim _ _} minimal = [∨]-introₗ [<]-minimum-lim
[≤]-to-[<][≡] (step xy) = [∨]-elim2 𝐒-increasing (congruence₁(𝐒)) ([≤]-to-[<][≡] xy)
[≤]-to-[<][≡] (maximal{p = inc}{i = i} xy) = [∨]-elim
  ([∨]-introₗ ∘ maximal)
  ([∨]-introₗ ∘ swap(subtransitivityₗ(_<_)(_≡_)) (maximal{i = 𝐒(i)} (𝐒-[ℕ≤][≤]-preserving-when-increasing inc)) ∘ congruence₁(𝐒))
  ([≤]-to-[<][≡] xy)
[≤]-to-[<][≡] (supremum xy) = {!!} -- TODO: Is this not possible to prove?
-}

_⋅_ : Ordinal → Ordinal → Ordinal
[⋅]ᵣ-weaklyIncreasing : Increasing(_≤_)(_≤_)(x ⋅_)
[⋅]ᵣ-increasing : (x > 𝟎) → Increasing(_<_)(_<_)(x ⋅_)

x ⋅ 𝟎       = 𝟎
x ⋅ 𝐒(y)    = (x ⋅ y) + x
𝟎           ⋅ lim f p = 𝟎
x@(𝐒 _)     ⋅ lim f p = lim(y ↦ (x ⋅ f(y))) ([⋅]ᵣ-increasing [<]-minimal ∘ p)
x@(lim _ _) ⋅ lim f p = lim(y ↦ (x ⋅ f(y))) ([⋅]ᵣ-increasing [<]-minimum-lim ∘ p)

instance
  [⋅]-absorberₗ : Absorberₗ(_⋅_)(𝟎)
  [⋅]-absorberₗ = intro(\{x} → proof{x}) where
    proof : Names.Absorberₗ(_⋅_)(𝟎)
    proof {𝟎}       = reflexivity(_≡_)
    proof {𝐒 x}     = proof{x}
    proof {lim f p} = reflexivity(_≡_)

[⋅]ᵣ-weaklyIncreasing {a} {.𝟎} {y} minimal = minimal
[⋅]ᵣ-weaklyIncreasing {a} {.(𝐒 _)} {.(𝐒 _)} (step ord) = [+]ₗ-weaklyIncreasing ([⋅]ᵣ-weaklyIncreasing ord)
[⋅]ᵣ-weaklyIncreasing {𝟎}       {.(𝐒 x)} {.(lim _ _)} (maximal {x = x} ord) = sub₂ (_≡_) (_≤_) (absorberₗ(_⋅_)(𝟎) {x})
[⋅]ᵣ-weaklyIncreasing {𝐒 a}     {.(𝐒 x)} {.(lim f _)} (maximal {f}{inc}{x}{i} ord) = maximal {i = 𝐒 i} $
  (𝐒(a) ⋅ x) + a       🝖[ _≤_ ]-[ [+]ₗ-weaklyIncreasing ([⋅]ᵣ-weaklyIncreasing ord) ]
  (𝐒(a) ⋅ f(i)) + a    🝖[ _≤_ ]-[ [≤]-of-𝐒 ]
  𝐒((𝐒(a) ⋅ f(i)) + a) 🝖[ _≤_ ]-[]
  (𝐒(a) ⋅ f(i)) + 𝐒(a) 🝖[ _≤_ ]-[]
  𝐒(a) ⋅ 𝐒(f(i))       🝖[ _≤_ ]-[ [⋅]ᵣ-weaklyIncreasing (𝐒-[ℕ≤][≤]-preserving-when-increasing inc) ]
  𝐒(a) ⋅ f(𝐒(i))       🝖-end
[⋅]ᵣ-weaklyIncreasing {lim f p} {.(𝐒 _)} {.(lim _ _)} (maximal{g}{inc}{x}{i} ord) = supremum \{j} → maximal{i = 𝐒 i} $
  (lim f p ⋅ x) + f(j)       🝖[ _≤_ ]-[ [+]-weaklyIncreasing ([⋅]ᵣ-weaklyIncreasing ord) (sub₂(_<_)(_≤_) [<]-limit) ]
  (lim f p ⋅ g(i)) + lim f p 🝖[ _≤_ ]-[]
  lim f p ⋅ 𝐒(g(i))          🝖[ _≤_ ]-[ [⋅]ᵣ-weaklyIncreasing (𝐒-[ℕ≤][≤]-preserving-when-increasing inc) ]
  lim f p ⋅ g(𝐒(i))          🝖-end
[⋅]ᵣ-weaklyIncreasing {𝟎} {.(lim _ _)} {y} (supremum ord) = minimal
[⋅]ᵣ-weaklyIncreasing {𝐒 a} {.(lim _ _)} {y} (supremum{g} ord) = supremum \{i} →
  𝐒(𝐒(a) ⋅ g(i))       🝖[ _≤_ ]-[ step [+]ₗ-order ]
  𝐒((𝐒(a) ⋅ g(i)) + a) 🝖[ _≤_ ]-[ [⋅]ᵣ-weaklyIncreasing {𝐒 a} (ord{i}) ]
  𝐒(a) ⋅ y             🝖-end
[⋅]ᵣ-weaklyIncreasing {lim f x} {.(lim _ _)} {y} (supremum{g} ord) = supremum \{i} → [⋅]ᵣ-increasing [<]-minimum-lim ord

[⋅]ᵣ-increasing {a} pos {x} {𝐒 y} (step ord) =
  a ⋅ x       🝖[ _≤_ ]-[ [⋅]ᵣ-weaklyIncreasing ord ]-sub
  a ⋅ y       🝖[ _<_ ]-[ [+]ₗ-strict-order pos ]-super
  (a ⋅ y) + a 🝖[ _≤_ ]-[]
  a ⋅ 𝐒(y)    🝖-end
[⋅]ᵣ-increasing {𝐒 a}     pos {x} {lim f p} (maximal{i = i} ord) = maximal{i = i} ([⋅]ᵣ-weaklyIncreasing {𝐒(a)} ord)
[⋅]ᵣ-increasing {lim g q} pos {x} {lim f p} (maximal{i = i} ord) = maximal{i = i} ([⋅]ᵣ-weaklyIncreasing {lim g q} ord)

instance
  [⋅]-absorberᵣ : Absorberᵣ(_⋅_)(𝟎)
  [⋅]-absorberᵣ = intro(reflexivity(_≡_))

instance
  [⋅]-identityᵣ : Identityᵣ(_⋅_)(𝟏)
  [⋅]-identityᵣ = intro \{x} →
    (x ⋅ 𝟏)     🝖[ _≡_ ]-[]
    (x ⋅ 𝐒(𝟎))  🝖[ _≡_ ]-[]
    (x ⋅ 𝟎) + x 🝖[ _≡_ ]-[]
    𝟎 + x       🝖[ _≡_ ]-[ identityₗ(_+_)(𝟎) ]
    x           🝖-end

instance
  [⋅]-identityₗ : Identityₗ(_⋅_)(𝟏)
  [⋅]-identityₗ = intro proof where
    proof : Names.Identityₗ(_⋅_)(𝟏)
    proof {𝟎} =
      𝟏 ⋅ 𝟎    🝖[ _≡_ ]-[]
      𝟎     🝖-end
    proof {𝐒 x} =
      (𝟏 ⋅ 𝐒(x))  🝖[ _≡_ ]-[]
      (𝟏 ⋅ x) + 𝟏 🝖[ _≡_ ]-[ congruence₁(𝐒) (proof{x}) ]
      x + 𝟏       🝖[ _≡_ ]-[]
      x + 𝐒(𝟎)    🝖[ _≡_ ]-[]
      𝐒(x + 𝟎)    🝖[ _≡_ ]-[]
      𝐒(x)        🝖-end
    proof {lim f p} =
      (𝟏 ⋅ lim f p)        🝖[ _≡_ ]-[]
      lim(\y → 𝟏 ⋅ f(y)) _ 🝖[ _≡_ ]-[ lim-function(\{x} → proof{f(x)}) ]
      lim f p              🝖-end

[⋅]ₗ-strict-order : (x > 𝟎) → (y > 𝟏) → (x < (x ⋅ y))
[⋅]ₗ-strict-order {x}{y} dom-x dom-y =
  x     🝖[ _≡_ ]-[ symmetry(_≡_) (identityₗ(_+_)(𝟎)) ]-sub
  𝟎 + x 🝖[ _<_ ]-[ [⋅]ᵣ-increasing {x} dom-x {𝟏}{y} dom-y ]-super
  x ⋅ y 🝖[ _≤_ ]-end

[⋅]-positive : (x > 𝟎) → (y > 𝟎) → ((x ⋅ y) > 𝟎)
[⋅]-positive {𝐒 x}     {𝐒 y}     pos-x pos-y = [<]-minimal
[⋅]-positive {𝐒 x}     {lim g q} pos-x pos-y = [<]-minimum-lim
[⋅]-positive {lim f p} {𝐒 y}     pos-x pos-y = [<]-minimum-lim
[⋅]-positive {lim f p} {lim g q} pos-x pos-y = [<]-minimum-lim

[⋅]ₗ-weaklyIncreasing : Increasing(_≤_)(_≤_)(_⋅ y)

_^_ : Ordinal → Ordinal → Ordinal
[^]ᵣ-weaklyIncreasing : Increasing(_≤_)(_≤_)(x ^_)
[^]ᵣ-increasing : (x > 𝟏) → Increasing(_<_)(_<_)(x ^_)
[^]-positive : (x > 𝟎) → ((x ^ y) > 𝟎)

𝟎-𝟏-alternatives : (x ≡ 𝟎) ∨ (x ≡ 𝟏) ∨ (x > 𝟏)
𝟎-𝟏-alternatives {𝟎}          = [∨]-introₗ ([∨]-introₗ (reflexivity(_≡_)))
𝟎-𝟏-alternatives {𝟏}          = [∨]-introₗ ([∨]-introᵣ (reflexivity(_≡_)))
𝟎-𝟏-alternatives {𝐒(𝐒 x)}     = [∨]-introᵣ (step(step minimal))
𝟎-𝟏-alternatives {𝐒(lim f p)} = [∨]-introᵣ (step [<]-minimum-lim)
𝟎-𝟏-alternatives {lim f p}    = [∨]-introᵣ ([<]-num-lim {𝟏})

-- Note: (𝟎 ^ 𝟎 = 𝟎) because it is convenient that Increasing(_≤_)(_≤_)(x ^_) is satisfied.
x ^ 𝟎    = 𝟏
x ^ 𝐒(y) = (x ^ y) ⋅ x
x ^ lim f p with 𝟎-𝟏-alternatives{x}
... | [∨]-introₗ ([∨]-introₗ _) = 𝟎
... | [∨]-introₗ ([∨]-introᵣ _) = 𝟏
... | [∨]-introᵣ gt             = lim (y ↦ (x ^ f(y))) ([^]ᵣ-increasing gt ∘ p)
{-
𝟎              ^ lim f p = 𝟎
𝟏              ^ lim f p = 𝟏
x@(𝐒(𝐒 _))     ^ lim f p = lim (y ↦ (x ^ f(y))) ([^]ᵣ-increasing (step(step minimal)) ∘ p)
x@(𝐒(lim _ _)) ^ lim f p = lim (y ↦ (x ^ f(y))) ([^]ᵣ-increasing (step [<]-minimum-lim) ∘ p)
x@(lim _ _)    ^ lim f p = lim (y ↦ (x ^ f(y))) ([^]ᵣ-increasing ([<]-num-lim {𝟏}) ∘ p)
-}

[^][𝟎]-almost-absorberₗ : (x > 𝟎) → ((𝟎 ^ x) ≡ 𝟎)
[^][𝟎]-almost-absorberₗ {𝐒 x}     pos = reflexivity(_≡_)
[^][𝟎]-almost-absorberₗ {lim f p} pos = reflexivity(_≡_)

instance
  [^]-absorberₗ : Absorberₗ(_^_)(𝟏)
  [^]-absorberₗ = intro(\{x} → p{x}) where
    p : Names.Absorberₗ(_^_)(𝟏)
    p {𝟎} = reflexivity(_≡_)
    p {𝐒 x} =
      𝟏 ^ 𝐒(x)                🝖[ _≡_ ]-[]
      (𝟏 ^ x) ⋅ 𝟏             🝖[ _≡_ ]-[]
      (𝟏 ^ x) ⋅ 𝟏             🝖[ _≡_ ]-[]
      ((𝟏 ^ x) ⋅ 𝟎) + (𝟏 ^ x) 🝖[ _≡_ ]-[]
      𝟎 + (𝟏 ^ x)             🝖[ _≡_ ]-[ identityₗ(_+_)(𝟎) ]
      𝟏 ^ x                   🝖[ _≡_ ]-[ p{x} ]
      𝟏                       🝖-end
    p {lim _ _} = reflexivity(_≡_)

instance
  [^]-identityᵣ : Identityᵣ(_^_)(𝟏)
  [^]-identityᵣ = intro(\{x} → p{x}) where
    p : Names.Identityᵣ(_^_)(𝟏)
    p {𝟎}         = reflexivity(_≡_)
    p {𝐒 x}       = congruence₁(𝐒) (identityₗ(_⋅_)(𝟏))
    p {lim f inc} = lim-function \{x} → p{f(x)}

[^]ₗ-order : (x ≤ 𝟏) ∨ (y > 𝟎) → (x ≤ (x ^ y))
[^]ₗ-order {x} {y} ([∨]-introₗ x1) with 𝟎-𝟏-alternatives {x}
... | [∨]-introₗ ([∨]-introₗ px) = subtransitivityₗ(_≤_)(_≡_) px minimal
... | [∨]-introₗ ([∨]-introᵣ px) = sub₂(_≡_)(_≤_) $
  x     🝖[ _≡_ ]-[ px ]
  𝟏     🝖[ _≡_ ]-[ absorberₗ(_^_)(𝟏) {y} ]-sym
  𝟏 ^ y 🝖[ _≡_ ]-[ {!!} ]
  x ^ y 🝖-end
... | [∨]-introᵣ px with step() ← transitivity(_≤_) px x1
[^]ₗ-order {x}{𝐒 y}     ([∨]-introᵣ y0) = {![⋅]ᵣ-order!}
[^]ₗ-order {x}{lim y p} ([∨]-introᵣ (maximal{i = i} y0)) with 𝟎-𝟏-alternatives {x}
... | [∨]-introₗ ([∨]-introₗ px) = sub₂(_≡_)(_≤_) px
... | [∨]-introₗ ([∨]-introᵣ px) = sub₂(_≡_)(_≤_) px
... | [∨]-introᵣ px = sub₂(_<_)(_≤_) (maximal{i = 𝐒(i)} ([^]ₗ-order {x}{y(𝐒(i))} ([∨]-introᵣ (transitivity(_≤_) (step y0) (𝐒-[ℕ≤][≤]-preserving-when-increasing p)))))

{-
[^]ₗ-order {𝟎}          {y}       ([∨]-introₗ x1) = minimal
[^]ₗ-order {𝐒 𝟎}        {y}       ([∨]-introₗ x1) = sub₂(_≡_)(_≥_) (absorberₗ(_^_)(𝟏) {y})
[^]ₗ-order {𝐒(𝐒 x)}     {y}       ([∨]-introₗ (step()))
[^]ₗ-order {𝐒(lim f p)} {y}       ([∨]-introₗ (step(supremum x1))) with () ← x1{𝟎}
[^]ₗ-order {lim f p}    {y}       ([∨]-introₗ (supremum x1))       with () ← [≤][>]-contradiction ([≤]-increasing-function-num-min {f}{𝟏}{p}) x1
[^]ₗ-order {x}          {𝐒 y}     ([∨]-introᵣ y0) = {![⋅]ᵣ-order!}
[^]ₗ-order {x}          {lim y p} ([∨]-introᵣ (maximal y0)) = {!y0!}
-}

[^]ᵣ-weaklyIncreasing {a} {.𝟎} {y} minimal = {![^][𝟎]-almost-absorberₗ {𝐒(a)}!}
[^]ᵣ-weaklyIncreasing {a} {.(𝐒 _)} {.(𝐒 _)} (step ord) = [⋅]ₗ-weaklyIncreasing {a} ([^]ᵣ-weaklyIncreasing ord)
[^]ᵣ-weaklyIncreasing {a} {𝐒 x} {.(lim _ _)} (maximal ord) with 𝟎-𝟏-alternatives {a}
... | [∨]-introₗ ([∨]-introₗ px) = {!!}
... | [∨]-introₗ ([∨]-introᵣ px) = {!!}
... | [∨]-introᵣ px = {!!}
[^]ᵣ-weaklyIncreasing {a} {lim f inc} {y} (supremum ord) with 𝟎-𝟏-alternatives {a}
... | [∨]-introₗ ([∨]-introₗ px) = minimal
... | [∨]-introₗ ([∨]-introᵣ px) = [^]-positive {a}{y} (sub₂(_≡_)(_≥_) px)
... | [∨]-introᵣ px = supremum \{i} → [^]ᵣ-increasing {a} px {f(i)}{y} ord
{-
[^]ᵣ-weaklyIncreasing {a} {.𝟎} {y} minimal = {!!} -- [^]ₗ-order {!!}
[^]ᵣ-weaklyIncreasing {a} {.(𝐒 x)} {.(𝐒 y)} (step {x} {y} ord) = [⋅]ₗ-weaklyIncreasing {a} ([^]ᵣ-weaklyIncreasing ord)
[^]ᵣ-weaklyIncreasing {𝟎} {.(𝐒 _)} {.(lim _ _)} (maximal ord) = minimal
[^]ᵣ-weaklyIncreasing {𝐒 𝟎} {.(𝐒 _)} {.(lim _ _)} (maximal ord) = {!!}
[^]ᵣ-weaklyIncreasing {𝐒 (𝐒 a)} {.(𝐒 _)} {.(lim _ _)} (maximal ord) = {!!}
[^]ᵣ-weaklyIncreasing {𝐒 (lim f x)} {.(𝐒 _)} {.(lim _ _)} (maximal ord) = {!!}
[^]ᵣ-weaklyIncreasing {lim f x} {.(𝐒 _)} {.(lim _ _)} (maximal ord) = {!!}
[^]ᵣ-weaklyIncreasing {a} {.(lim _ _)} {y} (supremum x) = {!!}
-}

[^]ᵣ-increasing {a} dom {x} (step {y = y} ord) =
  a ^ x       🝖[ _≤_ ]-[ [^]ᵣ-weaklyIncreasing ord ]-sub
  a ^ y       🝖[ _<_ ]-[ [⋅]ₗ-strict-order ([^]-positive {y = y} (transitivity(_<_) [<]-minimal dom)) dom ]-super
  (a ^ y) ⋅ a 🝖[ _≤_ ]-[]
  a ^ 𝐒(y)    🝖-end
[^]ᵣ-increasing {𝐒 𝟎}        (step()) (maximal _)
[^]ᵣ-increasing {𝐒(𝐒 a)}     dom      (maximal{i = i} ord) = maximal{i = i} ([^]ᵣ-weaklyIncreasing ord)
[^]ᵣ-increasing {𝐒(lim g q)} dom      (maximal{i = i} ord) = maximal{i = i} ([^]ᵣ-weaklyIncreasing ord)
[^]ᵣ-increasing {lim g q}    dom      (maximal{i = i} ord) = maximal{i = i} ([^]ᵣ-weaklyIncreasing ord)

[^]-positive {_}         {𝟎}       pos = step minimal
[^]-positive {𝐒 x}       {𝐒 y}     pos = [⋅]-positive ([^]-positive {𝐒 x}{y} pos) pos
[^]-positive {𝐒 𝟎}       {lim g q} pos = pos
[^]-positive {𝐒(𝐒 x)}    {lim g q} pos = [<]-minimum-lim
[^]-positive {𝐒(lim f x)}{lim g q} pos = [<]-minimum-lim
[^]-positive {lim f p}   {𝐒 y}     pos = [⋅]-positive ([^]-positive {lim f p}{y} pos) [<]-minimum-lim
[^]-positive {lim f p}   {lim g q} pos = [<]-minimum-lim
