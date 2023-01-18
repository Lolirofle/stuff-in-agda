module Miscellaneous.OrdinalNeg where

open import Functional
import      Lvl
open import Syntax.Function
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}
private variable f : T → T
private variable i n x y : T

data Ordinal : Type{Lvl.𝟎}
data _≤_ : Ordinal → Ordinal → Type{Lvl.𝟎}
_<_ : Ordinal → Ordinal → Type{Lvl.𝟎}

Increasing : (Ordinal → Ordinal) → Type
Increasing(f) = (∀{i₁ i₂} → (i₁ < i₂) → (f(i₁) < f(i₂))) 

WeaklyIncreasing : (Ordinal → Ordinal) → Type
WeaklyIncreasing(f) = (∀{i₁ i₂} → (i₁ ≤ i₂) → (f(i₁) ≤ f(i₂)))

{-# NO_POSITIVITY_CHECK #-}
data Ordinal where
  𝟎   : Ordinal
  𝐒   : Ordinal → Ordinal
  lim : (f : Ordinal → Ordinal) → (Increasing(f)) → Ordinal

x < y = 𝐒(x) ≤ y

data _≤_ where
  minimal  : ∀{x} → (𝟎 ≤ x)
  step     : ∀{x y} → (x ≤ y) → (𝐒(x) ≤ 𝐒(y))
  maximal  : ∀{f}{p : Increasing(f)}{x}{i} → (x ≤ f(i)) → (x < lim f p)
  supremum : ∀{f}{p : Increasing(f)}{x} → (∀{i} → (f(i) < x)) → (lim f p ≤ x)

module _
  {ℓ}
  (P : Ordinal → Type{ℓ})
  (p0 : P(𝟎))
  (ps : ∀{x} → P(x) → P(𝐒(x)))
  (pl : ∀{f}{p : Increasing(f)} → (∀{i} → P(f(i))) → P(lim f p))
  where

  elim : ((x : Ordinal) → P(x))
  elim 𝟎 = p0
  elim (𝐒(x)) = ps(elim x)
  elim (lim f p) = pl \{i} → elim(f(i))

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
  [<]-transitivity : Transitivity(_<_)
  [<]-transitivity = intro(subtransitivityᵣ(_≤_)(_<_))

instance
  [<]-asymmetry : Asymmetry(_<_)
  [<]-asymmetry = intro(irreflexivity(_<_) ∘₂ transitivity(_<_))

[<]-minimum-𝐒 : 𝟎 < 𝐒(x)
[<]-minimum-𝐒 = step minimal

[<]-𝐒-self : x < 𝐒(x)
[<]-𝐒-self = step(reflexivity(_≤_))

[≤]-𝐒-self : x ≤ 𝐒(x)
[≤]-𝐒-self = sub₂(_<_)(_≤_) [<]-𝐒-self

[<]-minimum-lim : ∀{p : Increasing(f)} → (𝟎 < lim f p)
[<]-minimum-lim = maximal{i = 𝟎} minimal

[<]-limit : ∀{p : Increasing(f)} → (f(i) < lim f p)
[<]-limit = maximal(reflexivity(_≤_))

𝐒-[≤]-preserving-when-increasing : Increasing(f) → (𝐒(f(i)) ≤ f(𝐒(i)))
𝐒-[≤]-preserving-when-increasing inc = inc [<]-𝐒-self

increasing-self : Increasing(f) → (i ≤ f(i))
increasing-self{i = 𝟎}       inc = minimal
increasing-self{i = 𝐒 i}     inc = transitivity(_≤_) (step(increasing-self{i = i} inc)) (𝐒-[≤]-preserving-when-increasing inc)
increasing-self{i = lim f p} inc = supremum \{i} → transitivity(_≤_) (𝐒-[≤]-preserving-when-increasing p) (transitivity(_≤_) (increasing-self{i = f(𝐒(i))} inc) (sub₂(_<_)(_≤_) (inc [<]-limit)))

{-
strictly-increasing-self : Increasing(f) → (𝟎 < f(𝟎)) → (i < f(i))
strictly-increasing-self{i = 𝟎}       inc nz = nz
strictly-increasing-self{i = 𝐒 i}     inc nz = subtransitivityᵣ(_<_)(_≤_) ⦃ {!!} ⦄ (step(strictly-increasing-self{i = i} inc nz)) (𝐒-[≤]-preserving-when-increasing inc)
strictly-increasing-self{i = lim f p} inc nz = subtransitivityₗ(_<_)(_≤_) ⦃ {!!} ⦄ (supremum \{i} → {!strictly-increasing-self{i = f(i)} inc nz!}) {!!}
-}

-- TODO: It is possible to define this…
what : Ordinal → Ordinal
what 𝟎 = 𝐒(𝟎)
what (𝐒 p) = 𝐒(𝐒 p)
what (lim f x) = f(lim f x)

open import Syntax.Transitivity

-- TODO: …and then this will be a invalid term (because it is non-terminating). The `p` term in `lim f p` should prevent this from happening, but it is not strong enough it seems.
what2 : Ordinal
what2 = what(lim what proof) where
  proof : Increasing what
  proof {𝟎} {𝐒 y} (step p) = step (step p)
  proof {𝐒 x} {𝐒 y} (step p) = step (step p)
  proof {lim f x} {𝐒 y} (step (supremum ord)) = transitivity(_≤_) ord (transitivity(_≤_) [≤]-𝐒-self [≤]-𝐒-self)
  proof {𝟎} {lim f inc} (maximal{i = i} ord) = subtransitivityₗ(_<_)(_≤_) (transitivity(_≤_) (step ord) (𝐒-[≤]-preserving-when-increasing inc)) (inc(maximal{i = 𝐒(i)} (increasing-self inc)))
  proof {𝐒 x} {lim f inc} (maximal{i = i} ord) = subtransitivityₗ(_<_)(_≤_) (transitivity(_≤_) (step ord) (𝐒-[≤]-preserving-when-increasing inc)) (inc (maximal{i = 𝐒(i)} (increasing-self inc)))
  proof {lim f inc-f} {lim g inc-g} (maximal{i = i}(supremum ord)) =
    f(lim f inc-f) 🝖[ _<_ ]-[ inc-f (step (supremum ord)) ]
    f(𝐒(g(i))) 🝖[ _<_ ]-[ ord ]
    g(i)       🝖-semiend
    g(lim g inc-g) 🝖[ _<_ ]-end-from-[ inc-g (maximal{i = i} (increasing-self inc-g)) ]

{-
open import Data
open import Numeral.Natural
open import Numeral.Natural.Induction
open import Syntax.Number

instance
  Ordinal-numeral : InfiniteNumeral(Ordinal)
  Ordinal-numeral = record { num = \n ⦃ _ ⦄ → ℕ-elim(const Ordinal) 𝟎 (const 𝐒) n }

ω : Ordinal
ω = lim id id

ω1 : Ordinal
ω1 = lim 𝐒 step

ω2 : Ordinal
ω2 = lim (𝐒 ∘ 𝐒) (step ∘ step)

test : ω1 < ω2
test = maximal{i = ω1} {!!}

[≤]-of-ω : num(n) < ω1
[≤]-of-ω {𝟎} = [<]-minimum-lim
[≤]-of-ω {𝐒 n} = maximal{i = ω1} (step(sub₂(_<_)(_≤_) ([≤]-of-ω {n})))

_+_ : Ordinal → Ordinal → Ordinal
[+]ₗ-increasing : ∀{f} → Increasing(f) → ∀{x} → Increasing(y ↦ x + f(y))
[+]ᵣ-increasing : ∀{x} → Increasing(x +_)
[+]ᵣ-weaklyIncreasing : ∀{x} → WeaklyIncreasing(x +_)

x + 𝟎       = x
x + 𝐒(y)    = 𝐒(x + y)
x + lim f p = lim(y ↦ (x + f(y))) ([+]ₗ-increasing p)

[+]ᵣ-weaklyIncreasing {𝟎} {i₁ = .𝟎} {i₂} minimal = minimal
[+]ᵣ-weaklyIncreasing {𝐒 x} {i₁ = .𝟎} {𝟎} minimal = step ([+]ᵣ-weaklyIncreasing minimal)
[+]ᵣ-weaklyIncreasing {𝐒 x} {i₁ = .𝟎} {𝐒 i₂} minimal = step (sub₂(_<_)(_≤_) ([+]ᵣ-weaklyIncreasing {𝐒 x} {i₁ = 𝟎} {i₂} minimal))
[+]ᵣ-weaklyIncreasing {𝐒 x} {i₁ = .𝟎} {lim f x₁} minimal = maximal{i = 𝟎} (sub₂(_<_)(_≤_) ([+]ᵣ-weaklyIncreasing {𝐒 x} {i₁ = 𝟎} {f _} minimal))
[+]ᵣ-weaklyIncreasing {lim f p} {i₁ = .𝟎} {𝟎} minimal = reflexivity(_≤_)
[+]ᵣ-weaklyIncreasing {lim f p} {i₁ = .𝟎} {𝐒 i₂} minimal = supremum (step {!!})
[+]ᵣ-weaklyIncreasing {lim f p} {i₁ = .𝟎} {lim f₁ x₁} minimal = {!maximal!}
[+]ᵣ-weaklyIncreasing {x} {i₁ = .(𝐒 _)} {.(𝐒 _)} (step ord) = step ([+]ᵣ-weaklyIncreasing ord)
[+]ᵣ-weaklyIncreasing {x} {i₁ = .(𝐒 _)} {.(lim _ _)} (maximal ord) = maximal ([+]ᵣ-weaklyIncreasing ord)
[+]ᵣ-weaklyIncreasing {x} {i₁ = .(lim _ _)} {i₂} (supremum x₁) = supremum ([+]ᵣ-weaklyIncreasing x₁)

{-[+]ₗ-increasing inc (step ord) = {!!}
[+]ₗ-increasing inc (maximal ord) = {!!}

[+]ᵣ-weaklyIncreasing {𝟎} minimal = minimal
[+]ᵣ-weaklyIncreasing {𝐒 x} {i₂ = 𝟎} minimal = step {!!}
[+]ᵣ-weaklyIncreasing {𝐒 x} {i₂ = 𝐒 i₂} minimal = step {!!}
[+]ᵣ-weaklyIncreasing {𝐒 x} {i₂ = lim f x₁} minimal = {!!}
[+]ᵣ-weaklyIncreasing {lim f x} minimal = {!!}
[+]ᵣ-weaklyIncreasing (step ord) = {!!}
[+]ᵣ-weaklyIncreasing (maximal ord) = {!!}
[+]ᵣ-weaklyIncreasing (supremum x) = {!!}

[+]ᵣ-increasing (step ord) = step {![+]ᵣ-increasing !}
[+]ᵣ-increasing (maximal ord) = {!!}
-}

_⋅_ : Ordinal → Ordinal → Ordinal
x ⋅ 𝟎       = 𝟎
x ⋅ 𝐒(y)    = (x ⋅ y) + x
x ⋅ lim f p = lim(y ↦ (x ⋅ f(y))) {!!}

_^_ : Ordinal → Ordinal → Ordinal
x ^ 𝟎       = x
x ^ 𝐒(y)    = (x ^ y) ⋅ x
x ^ lim f p = lim(y ↦ (x ^ f(y))) {!!}
-}
