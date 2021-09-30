{-# OPTIONS --cubical #-}

module Miscellaneous.LimNatural where

import      Lvl
open import Numeral.Natural as ℕ using (ℕ)
open import Numeral.Sign as Sign using (−|+ ; −|0|+ ; ➖ ; ➕)
open import Type.Cubical
open import Type.Cubical.Path.Equality
open import Type

data ℕ∞ : Type{Lvl.𝟎} where
  𝟎 : ℕ∞
  𝐒 : ℕ∞ → ℕ∞
  ∞ : ℕ∞
  𝐒-fixpoint : (𝐒(∞) ≡ ∞)

𝐏₀ : ℕ∞ → ℕ∞
𝐏₀(𝟎)    = 𝟎
𝐏₀(𝐒(n)) = n
𝐏₀(∞)    = ∞
𝐏₀(𝐒-fixpoint i) = ∞

_+_ : ℕ∞ → ℕ∞ → ℕ∞
x + 𝟎    = x
x + 𝐒(y) = 𝐒(x + y)
_ + ∞    = ∞
x + 𝐒-fixpoint i = 𝐒-fixpoint i
infixl 10010 _+_

_⋅_ : ℕ∞ → ℕ∞ → ℕ∞
x ⋅ 𝟎    = 𝟎
x ⋅ 𝐒(y) = x + (x ⋅ y)
x ⋅ ∞    = ∞
x ⋅ 𝐒-fixpoint i = ∞
infixl 10020 _⋅_

open import Data.Boolean
open import Data.Boolean.Stmt
open import Functional
open import Type.Cubical.Path.Proofs

isFinite : ℕ∞ → Bool
isFinite 𝟎      = 𝑇
isFinite (𝐒(n)) = isFinite n
isFinite ∞      = 𝐹
isFinite (𝐒-fixpoint i) = 𝐹

isZero : ℕ∞ → Bool
isZero 𝟎     = 𝑇
isZero (𝐒 _) = 𝐹
isZero ∞     = 𝐹
isZero (𝐒-fixpoint i) = 𝐹

_≤?_ : ℕ∞ → ℕ∞ → Bool
𝟎    ≤? _    = 𝑇
𝐒(x) ≤? 𝟎    = 𝐹
𝐒(x) ≤? 𝐒(y) = x ≤? y
𝐒(x) ≤? ∞    = 𝑇
∞    ≤? 𝟎    = 𝐹
∞    ≤? 𝐒(y) = ∞ ≤? y
∞    ≤? ∞    = 𝑇
𝐒(𝟎)            ≤? 𝐒-fixpoint _ = 𝑇
𝐒(𝐒(x))         ≤? 𝐒-fixpoint _ = 𝑇
𝐒(∞)            ≤? 𝐒-fixpoint _ = 𝑇
𝐒(𝐒-fixpoint _) ≤? 𝐒-fixpoint _ = 𝑇
∞               ≤? 𝐒-fixpoint _ = 𝑇
𝐒-fixpoint _    ≤? 𝟎            = 𝐹
𝐒-fixpoint _    ≤? 𝐒(y)         = ∞ ≤? y
𝐒-fixpoint _    ≤? ∞            = 𝑇
𝐒-fixpoint _    ≤? 𝐒-fixpoint _ = 𝑇

_≤_ : ℕ∞ → ℕ∞ → Type
_≤_ = IsTrue ∘₂ (_≤?_)

open import Data
open import Structure.Function.Domain
open import Structure.Function
open import Structure.Relator.Properties
import      Structure.Relator.Names as Names
open import Syntax.Transitivity
open import Type.Cubical.Path.Proofs

private variable x y z : ℕ∞

𝐒-∞-involutive : (𝐒(𝐒(∞)) ≡ ∞)
𝐒-∞-involutive = congruence₁(𝐒) 𝐒-fixpoint 🝖 𝐒-fixpoint

instance
  𝐒-injectivity : Injective(𝐒)
  Injective.proof 𝐒-injectivity = congruence₁(𝐏₀)

[+]-baseₗ : (𝟎 + x ≡ x)
[+]-baseₗ {𝟎}   = reflexivity(_≡_)
[+]-baseₗ {𝐒 x} = congruence₁(𝐒) ([+]-baseₗ {x})
[+]-baseₗ {∞}   = reflexivity(_≡_)
[+]-baseₗ {𝐒-fixpoint i} = reflexivity(_≡_) {𝐒-fixpoint i}

[+]-stepₗ : (𝐒(x) + y ≡ 𝐒(x + y))
[+]-stepₗ {x} {𝟎}   = reflexivity(_≡_)
[+]-stepₗ {x} {𝐒 y} = congruence₁(𝐒) ([+]-stepₗ {x}{y})
[+]-stepₗ {x} {∞}   = symmetry(_≡_) 𝐒-fixpoint
[+]-stepₗ {x} {𝐒-fixpoint i} = symmetry(_≡_) (Interval.hComp diagram {!𝐒-fixpoint-fixpoint i!}) where
  diagram : Interval → Interval.Partial(Interval.farBound i) _
  diagram _ (i = Interval.𝟎) = congruence₁(𝐒) 𝐒-fixpoint
  diagram _ (i = Interval.𝟏) = 𝐒-fixpoint
  
  {-
  i0 j0 𝐒∞
  i0 j1 𝐒𝐒∞
  i1 j0 ∞
  i1 j1 𝐒∞
  -}
  -- test : ∀{i} → (𝐒(𝐒-fixpoint i) ≡ 𝐒-fixpoint i)
  -- test {i} j = {!!}
  {-
  i0 j0 𝐒𝐒∞
  i0 j1 𝐒∞
  i1 j0 𝐒∞
  i1 j1 ∞
  -}

open import Structure.Operator.Properties
import      Structure.Operator.Names as Names

instance
  [+]-identityᵣ : Identityᵣ(_+_)(𝟎)
  Identityᵣ.proof [+]-identityᵣ = reflexivity(_≡_)

instance
  [+]-identityₗ : Identityₗ(_+_)(𝟎)
  [+]-identityₗ = intro proof where
    proof : Names.Identityₗ(_+_)(𝟎)
    proof {𝟎}   = reflexivity(_≡_)
    proof {𝐒 x} = congruence₁(𝐒) (proof{x})
    proof {∞}   = reflexivity(_≡_)
    proof {𝐒-fixpoint i} = reflexivity(_≡_)

instance
  [+]-absorberᵣ : Absorberᵣ(_+_)(∞)
  Absorberᵣ.proof [+]-absorberᵣ = reflexivity(_≡_)

instance
  [+]-absorberₗ : Absorberₗ(_+_)(∞)
  [+]-absorberₗ = intro(\{x} → proof{x}) where
    proof : Names.Absorberₗ(_+_)(∞)
    proof {𝟎}   = reflexivity(_≡_)
    proof {𝐒 x} = congruence₁(𝐒) (proof{x}) 🝖 𝐒-fixpoint
    proof {∞}   = reflexivity(_≡_)
    proof {𝐒-fixpoint i} = {!!}

open import Data.Option as Option using (Option ; Some ; None)
import      Data.Option.Functions as Option

to-ℕ : ℕ∞ → Option(ℕ)
to-ℕ 𝟎     = Some ℕ.𝟎
to-ℕ (𝐒 n) = Option.map ℕ.𝐒(to-ℕ n)
to-ℕ ∞     = None
to-ℕ (𝐒-fixpoint i) = None

from-ℕ : ℕ → ℕ∞
from-ℕ ℕ.𝟎      = 𝟎
from-ℕ (ℕ.𝐒(n)) = 𝐒(from-ℕ(n))

to-ℕ-finite : (n : ℕ∞) → ⦃ IsTrue(isFinite n) ⦄ → ℕ
to-ℕ-finite 𝟎     = ℕ.𝟎
to-ℕ-finite (𝐒 n) = ℕ.𝐒(to-ℕ-finite n)

open import Type.Identity
open import Type.Identity.Proofs

open import Data.Boolean.Equiv.Path
open import Data.Option.Equiv.Path
open import Numeral.Natural.Equiv.Path

𝟎-∞-inequality : (𝟎 ≢ ∞)
𝟎-∞-inequality = Bool-different-values ∘ congruence₁(not) ∘ congruence₁(isFinite)

𝟎-𝐒-inequality : ∀{x} → (𝟎 ≢ 𝐒(x))
𝟎-𝐒-inequality = Bool-different-values ∘ congruence₁(not) ∘ congruence₁(isZero)

instance
  from-ℕ-function : Function ⦃ Id-equiv ⦄ ⦃ Path-equiv ⦄ from-ℕ
  Function.congruence from-ℕ-function intro = reflexivity(_≡_)

instance
  to-ℕ-function : Function ⦃ Path-equiv ⦄ ⦃ Id-equiv ⦄ to-ℕ
  Function.congruence to-ℕ-function = sub₂(_≡_)(Id) ∘ congruence₁(to-ℕ)

open import Logic.Predicate
open import Logic.Propositional
open import Structure.Function.Domain
import      Structure.Function.Names as Names
open import Structure.Function.Domain.Proofs
open import Type.Size

instance
  ℕ∞-bijection : (ℕ∞ ≍ Option(ℕ)) ⦃ Path-equiv ⦄ ⦃ Id-equiv ⦄
  ∃.witness ℕ∞-bijection = to-ℕ
  ∃.proof ℕ∞-bijection = {!inverse-to-bijective ⦃ _ ⦄ ⦃ _ ⦄ {f = Option.partialMap ∞ from-ℕ}{f⁻¹ = to-ℕ}!} where
    invₗ : Names.Inverses (Option.partialMap ∞ from-ℕ) to-ℕ
    invₗ {𝟎}   = reflexivity(_≡_)
    invₗ {𝐒 x} =
      (Option.partialMap ∞ from-ℕ ∘ to-ℕ) (𝐒(x))          🝖[ _≡_ ]-[]
      Option.partialMap ∞ from-ℕ (Option.map ℕ.𝐒(to-ℕ x)) 🝖[ _≡_ ]-[ {!!} ]
      Option.partialMap ∞ (from-ℕ ∘ ℕ.𝐒) (to-ℕ x)         🝖[ _≡_ ]-[ {!!} ]
      Option.partialMap ∞ (𝐒 ∘ from-ℕ) (to-ℕ x)           🝖[ _≡_ ]-[ {!!} ]
      𝐒(Option.partialMap ∞ from-ℕ (to-ℕ x))              🝖[ _≡_ ]-[ congruence₁(𝐒) (invₗ{x}) ]
      𝐒(x) 🝖-end
    invₗ {∞}   = reflexivity(_≡_)
    invₗ {𝐒-fixpoint i} = {!!}

    invᵣ : Names.Inverses to-ℕ (Option.partialMap ∞ from-ℕ)
    invᵣ {None}          = reflexivity(_≡_)
    invᵣ {Some ℕ.𝟎}      = reflexivity(_≡_)
    invᵣ {Some (ℕ.𝐒(x))} =
      (to-ℕ ∘ Option.partialMap ∞ from-ℕ) (Some(ℕ.𝐒 x)) 🝖[ _≡_ ]-[]
      to-ℕ (from-ℕ (ℕ.𝐒(x)))                            🝖[ _≡_ ]-[]
      to-ℕ (𝐒(from-ℕ x))                                🝖[ _≡_ ]-[]
      Option.map ℕ.𝐒(to-ℕ(from-ℕ x))                    🝖[ _≡_ ]-[ congruence₁(Option.map ℕ.𝐒) (invᵣ {Some x}) ]
      Option.map ℕ.𝐒 (Some x)                           🝖[ _≡_ ]-[]
      Some(ℕ.𝐒 x)                                       🝖-end

    instance
      inv : Inverse to-ℕ (Option.partialMap ∞ from-ℕ)
      inv = [∧]-intro (intro invₗ) (intro invᵣ)
  {-injective-surjective-to-bijective ⦃ _ ⦄ ⦃ _ ⦄ (to-ℕ) where
    instance
      inj : Injective ⦃ Path-equiv ⦄ ⦃ Id-equiv ⦄ (to-ℕ)
      Injective.proof inj {x}{y} p = {!!}
    instance
      surj : Surjective ⦃ Id-equiv ⦄ (to-ℕ)-}

instance
  [≤]-reflexivity : Reflexivity(_≤_)
  [≤]-reflexivity = intro(\{x} → p{x}) where
    p : Names.Reflexivity(_≤_)
    p{𝟎}   = <>
    p{𝐒 x} = p{x}
    p{∞}   = <>
    p{𝐒-fixpoint i} = <>

[≤]ᵣ-of-∞ : ∀{x} → (x ≤ ∞)
[≤]ᵣ-of-∞ {𝟎}    = <>
[≤]ᵣ-of-∞ {𝐒(x)} = <>
[≤]ᵣ-of-∞ {∞}    = <>
[≤]ᵣ-of-∞ {𝐒-fixpoint i} = <>

[≤]ₗ-of-∞ : ∀{x} → (∞ ≤ x) → (x ≡ ∞)
[≤]ₗ-of-∞ {∞}       p = reflexivity(_≡_)
[≤]ₗ-of-∞ {𝐒 ∞}     p = 𝐒-fixpoint
[≤]ₗ-of-∞ {𝐒 (𝐒 x)} p = congruence₁(𝐒) ([≤]ₗ-of-∞ {𝐒 x} p) 🝖 𝐒-fixpoint
[≤]ₗ-of-∞ {𝐒(𝐒-fixpoint i)} p = {!!}
[≤]ₗ-of-∞ {𝐒-fixpoint i} p = {!𝐒-fixpoint!}

[≤]-antisymmetry : Antisymmetry(_≤_)(_≡_)
[≤]-antisymmetry = intro(\{x} → p{x}) where
  p : Names.Antisymmetry(_≤_)(_≡_)
  p {𝟎}   {𝟎}   ab ba = reflexivity(_≡_)
  p {𝐒 a} {𝐒 b} ab ba = congruence₁(𝐒) (p{a}{b} ab ba)
  p {𝐒 a} {∞}   ab ba = congruence₁(𝐒) (p{a}{∞} ([≤]ᵣ-of-∞{a}) ba) 🝖 𝐒-fixpoint
  p {∞}   {𝐒 b} ab ba = {!!}
  p {∞}   {∞}   ab ba = reflexivity(_≡_)
  p {𝐒 a} {𝐒-fixpoint i} ab ba = {!!}
  p {∞} {𝐒-fixpoint i} ab ba = {!!}
  p {𝐒-fixpoint i} {𝐒 b} ab ba = {!!}
  p {𝐒-fixpoint i} {∞} ab ba = {!!}
  p {𝐒-fixpoint i} {𝐒-fixpoint i₁} ab ba = {!!}
