module Numeral.Integer.Proofs where

import      Data.Either as Either
open import Data.Tuple  as Tuple using (_,_)
open import Logic
import      Lvl
open import Functional
open import Numeral.Integer
open import Numeral.Integer.Oper
open import Numeral.Integer.Sign
open import Numeral.Natural.Induction
open import Numeral.Natural as ℕ using (ℕ)
open import Numeral.Natural.UnclosedOper using () renaming (_−_ to _−ₙ_ ; signed0 to signedℕ)
import      Numeral.Natural.Oper as ℕ
import      Numeral.Natural.Oper.Proofs as ℕ
import      Numeral.Sign as Sign
import      Numeral.Sign.Oper0 as Sign
import      Numeral.Sign.Proofs as Sign
open import Lang.Inspect
open import Logic.IntroInstances
open import Logic.Propositional
open import Logic.Predicate
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Function.Multi
import      Structure.Function.Names as Names
open import Structure.Operator
open import Structure.Operator.Group
open import Structure.Operator.Monoid
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Operator.Proofs
open import Structure.Operator.Ring
open import Structure.OrderedField
open import Structure.Relator.Properties
open import Syntax.Number
open import Syntax.Transitivity
open import Type

private variable ℓ : Lvl.Level

-- TODO: Prove the usual structures for ℤ

instance
  [+ₙ][𝐒]-preserving : Preserving₁(+ₙ_) ℕ.𝐒 𝐒
  [+ₙ][𝐒]-preserving = intro [≡]-intro

instance
  [+ₙ][+]-preserving : Preserving₂(+ₙ_) (ℕ._+_) (_+_)
  [+ₙ][+]-preserving = intro [≡]-intro

instance
  [+ₙ][⋅]-preserving : Preserving₂(+ₙ_) (ℕ._⋅_) (_⋅_)
  Preserving.proof [+ₙ][⋅]-preserving {ℕ.𝟎}   {ℕ.𝟎}   = [≡]-intro
  Preserving.proof [+ₙ][⋅]-preserving {ℕ.𝟎}   {ℕ.𝐒 y} = [≡]-intro
  Preserving.proof [+ₙ][⋅]-preserving {ℕ.𝐒 x} {ℕ.𝟎}   = [≡]-intro
  Preserving.proof [+ₙ][⋅]-preserving {ℕ.𝐒 x} {ℕ.𝐒 y} = [≡]-intro

-- [−₀]-preserving : Preserving₂(+ₙ_) (_−₀ₙ_) (_−₀_)
-- [/₀]-preserving : Preserving₂(+ₙ_) (_/₀ₙ_) (_/₀_)

instance
  [−ₙ][𝐒][𝐏]-preserving : Preserving₁(−ₙ_) ℕ.𝐒 𝐏
  Preserving.proof [−ₙ][𝐒][𝐏]-preserving {ℕ.𝟎}   = [≡]-intro
  Preserving.proof [−ₙ][𝐒][𝐏]-preserving {ℕ.𝐒 x} = [≡]-intro

instance
  [−ₙ][+]-preserving : Preserving₂(−ₙ_) (ℕ._+_) (_+_)
  Preserving.proof [−ₙ][+]-preserving {ℕ.𝟎}    {ℕ.𝟎}    = [≡]-intro
  Preserving.proof [−ₙ][+]-preserving {ℕ.𝟎}    {ℕ.𝐒(_)} = [≡]-intro
  Preserving.proof [−ₙ][+]-preserving {ℕ.𝐒(_)} {ℕ.𝟎}    = [≡]-intro
  Preserving.proof [−ₙ][+]-preserving {ℕ.𝐒(_)} {ℕ.𝐒(_)} = [≡]-intro

instance
  [−][𝐒][𝐏]-preserving : Preserving₁(−_) 𝐒 𝐏
  Preserving.proof [−][𝐒][𝐏]-preserving {+ₙ ℕ.𝟎}    = [≡]-intro
  Preserving.proof [−][𝐒][𝐏]-preserving {+ₙ ℕ.𝐒 x}  = [≡]-intro
  Preserving.proof [−][𝐒][𝐏]-preserving {−𝐒ₙ ℕ.𝟎}   = [≡]-intro
  Preserving.proof [−][𝐒][𝐏]-preserving {−𝐒ₙ ℕ.𝐒 x} = [≡]-intro

instance
  [−𝐒ₙ][𝐒][𝐏]-preserving : Preserving₁(−𝐒ₙ_) ℕ.𝐒 𝐏
  Preserving.proof [−𝐒ₙ][𝐒][𝐏]-preserving = [≡]-intro

instance
  [+𝐒ₙ][𝐒]-preserving : Preserving₁(+𝐒ₙ_) ℕ.𝐒 𝐒
  Preserving.proof [+𝐒ₙ][𝐒]-preserving = [≡]-intro

instance
  [−][+]-preserving : Preserving₂(−_) (_+_)(_+_)
  Preserving.proof [−][+]-preserving {x}{y} = p{x}{y} where
    [−ₙ]-distribute-[−] : ∀{x y} → (−(x −ₙ y) ≡ y −ₙ x)
    [−ₙ]-distribute-[−] {ℕ.𝟎}   {ℕ.𝟎}   = [≡]-intro
    [−ₙ]-distribute-[−] {ℕ.𝟎}   {ℕ.𝐒 x} = [≡]-intro
    [−ₙ]-distribute-[−] {ℕ.𝐒 x} {ℕ.𝟎}   = [≡]-intro
    [−ₙ]-distribute-[−] {ℕ.𝐒 x} {ℕ.𝐒 y} = [−ₙ]-distribute-[−] {x} {y}

    p : Names.Preserving₂(−_) (_+_)(_+_)
    p {+ₙ ℕ.𝟎}    {+ₙ ℕ.𝟎}        = [≡]-intro
    p {+ₙ ℕ.𝟎}    {+ₙ ℕ.𝐒 y}      = [≡]-intro
    p {+ₙ ℕ.𝐒 x}  {+ₙ ℕ.𝟎}        = [≡]-intro
    p {+ₙ ℕ.𝐒 x}  {+ₙ ℕ.𝐒 y}      = [≡]-intro
    p {+ₙ ℕ.𝟎}    {−𝐒ₙ ℕ.𝟎}       = [≡]-intro
    p {+ₙ ℕ.𝟎}    {−𝐒ₙ ℕ.𝐒 y}     = [≡]-intro
    p {+ₙ ℕ.𝐒 x}  {−𝐒ₙ y}         = [−ₙ]-distribute-[−] {x}{y}
    p {−𝐒ₙ x}     {+ₙ ℕ.𝐒 y}      = [−ₙ]-distribute-[−] {y}{x}
    p {−𝐒ₙ ℕ.𝟎}   {+ₙ ℕ.𝟎}        = [≡]-intro
    p {−𝐒ₙ ℕ.𝟎}   {−𝐒ₙ ℕ.𝟎}       = [≡]-intro
    p {−𝐒ₙ ℕ.𝟎}   {−𝐒ₙ ℕ.𝐒 y}     = [≡]-intro
    p {−𝐒ₙ ℕ.𝐒 x} {−𝐒ₙ ℕ.𝟎}       = [≡]-intro
    p {−𝐒ₙ ℕ.𝐒 x} {−𝐒ₙ ℕ.𝐒 y}     = [≡]-intro
    p {−𝐒ₙ ℕ.𝐒 x} {+ₙ ℕ.𝟎}        = [≡]-intro



[ℤ]-non-negative-induction : ∀{P : ℤ → Type{ℓ}} → P(𝟎) → (∀(n) → P(+ₙ(n)) → P(+𝐒ₙ(n))) → (∀{n} → P(+ₙ n))
[ℤ]-non-negative-induction {P = P} = [ℕ]-induction {φ = P ∘ +ₙ_}

[ℤ]-positive-induction : ∀{P : ℤ → Type{ℓ}} → P(+𝐒ₙ(ℕ.𝟎)) → (∀(n) → P(+𝐒ₙ(n)) → P(+𝐒ₙ(ℕ.𝐒(n)))) → (∀{n} → P(+𝐒ₙ n))
[ℤ]-positive-induction {P = P} [1] [+] {ℕ.𝟎}   = [1]
[ℤ]-positive-induction {P = P} [1] [+] {ℕ.𝐒 n} = [+] n ([ℤ]-positive-induction {P = P} [1] [+] {n})

[ℤ]-non-positive-induction : ∀{P : ℤ → Type{ℓ}} → P(𝟎) → (∀(n) → P(−ₙ(n)) → P(−𝐒ₙ(n))) → (∀{n} → P(−ₙ n))
[ℤ]-non-positive-induction {P = P} [0] [−] {ℕ.𝟎}   = [0]
[ℤ]-non-positive-induction {P = P} [0] [−] {ℕ.𝐒 n} = [−] n ([ℤ]-non-positive-induction {P = P} [0] [−] {n})

[ℤ]-negative-induction : ∀{P : ℤ → Type{ℓ}} → P(−𝐒ₙ(ℕ.𝟎)) → (∀(n) → P(−𝐒ₙ(n)) → P(−𝐒ₙ(ℕ.𝐒(n)))) → (∀{n} → P(−𝐒ₙ n))
[ℤ]-negative-induction {P = P} = [ℕ]-induction {φ = P ∘ −𝐒ₙ_}

-- An intuitive induction proof method on integers
[ℤ]-intuitive-induction : ∀{P : ℤ → Type{ℓ}} → (∀{n} → P(−ₙ n) → P(−𝐒ₙ(n))) → P(𝟎) → (∀{n} → P(+ₙ n) → P(+𝐒ₙ(n))) → (∀{n} → P(n))
[ℤ]-intuitive-induction {P = P} [−] [0] [+] {𝟎}           = [0]
[ℤ]-intuitive-induction {P = P} [−] [0] [+] {+𝐒ₙ(n)}      = [+] ([ℤ]-intuitive-induction {P = P} [−] [0] [+] {+ₙ n})
[ℤ]-intuitive-induction {P = P} [−] [0] [+] {−𝐒ₙ(ℕ.𝟎)}    = [−] ([0])
[ℤ]-intuitive-induction {P = P} [−] [0] [+] {−𝐒ₙ(ℕ.𝐒(n))} = [−] ([ℤ]-intuitive-induction {P = P} [−] [0] [+] {−𝐒ₙ(n)})



[−𝐒ₙ]-equality : ∀{n} → (−𝐒ₙ(n) ≡ −ₙ(ℕ.𝐒(n)))
[−𝐒ₙ]-equality = [≡]-intro

[+𝐒ₙ]-equality : ∀{n} → (+𝐒ₙ(n) ≡ +ₙ(ℕ.𝐒(n)))
[+𝐒ₙ]-equality = [≡]-intro

-- (−n)−1 = −(n+1)
[𝐏]-negative : ∀{n} → (𝐏(−ₙ n) ≡ −𝐒ₙ(n))
[𝐏]-negative {ℕ.𝟎}    = [≡]-intro
[𝐏]-negative {ℕ.𝐒(n)} = [≡]-intro

-- (−(n+1))+1 = −n
[𝐒][−𝐒ₙ]-negative-identity : ∀{n} → (𝐒(−𝐒ₙ(n)) ≡ −ₙ n)
[𝐒][−𝐒ₙ]-negative-identity {ℕ.𝟎}    = [≡]-intro
[𝐒][−𝐒ₙ]-negative-identity {ℕ.𝐒(n)} = [≡]-intro

instance
  [𝐒][𝐏]-inverse : Inverse(𝐒)(𝐏)
  Inverseᵣ.proof (Tuple.left [𝐒][𝐏]-inverse)  {+ₙ  ℕ.𝟎}   = [≡]-intro
  Inverseᵣ.proof (Tuple.left [𝐒][𝐏]-inverse)  {+ₙ  ℕ.𝐒 x} = [≡]-intro
  Inverseᵣ.proof (Tuple.left [𝐒][𝐏]-inverse)  {−𝐒ₙ ℕ.𝟎}   = [≡]-intro
  Inverseᵣ.proof (Tuple.left [𝐒][𝐏]-inverse)  {−𝐒ₙ ℕ.𝐒 x} = [≡]-intro
  Inverseᵣ.proof (Tuple.right [𝐒][𝐏]-inverse) {+ₙ  ℕ.𝟎}   = [≡]-intro
  Inverseᵣ.proof (Tuple.right [𝐒][𝐏]-inverse) {+ₙ  ℕ.𝐒 x} = [≡]-intro
  Inverseᵣ.proof (Tuple.right [𝐒][𝐏]-inverse) {−𝐒ₙ ℕ.𝟎}   = [≡]-intro
  Inverseᵣ.proof (Tuple.right [𝐒][𝐏]-inverse) {−𝐒ₙ ℕ.𝐒 x} = [≡]-intro



[−ₙ]-identityᵣ : ∀{x} → (x −ₙ ℕ.𝟎 ≡ +ₙ x)
[−ₙ]-identityᵣ = [≡]-intro

[−ₙ]-antiidentityₗ : ∀{x} → (ℕ.𝟎 −ₙ x ≡ −ₙ x)
[−ₙ]-antiidentityₗ {ℕ.𝟎}    = [≡]-intro
[−ₙ]-antiidentityₗ {ℕ.𝐒(_)} = [≡]-intro

[−ₙ][𝐒]-step : ∀{x y} → (ℕ.𝐒(x) −ₙ y ≡ 𝐒(x −ₙ y))
[−ₙ][𝐒]-step {ℕ.𝟎}   {ℕ.𝟎}    = [≡]-intro
[−ₙ][𝐒]-step {ℕ.𝟎}   {ℕ.𝐒(y)} = [−ₙ]-antiidentityₗ {y} 🝖 symmetry(_≡_) ([𝐒][−𝐒ₙ]-negative-identity{y})
[−ₙ][𝐒]-step {ℕ.𝐒(_)}{ℕ.𝟎}    = [≡]-intro
[−ₙ][𝐒]-step {ℕ.𝐒(x)}{ℕ.𝐒(y)} = [−ₙ][𝐒]-step {x}{y}

[−][−ₙ] : ∀{x} → (−(+ₙ x) ≡ −ₙ x)
[−][−ₙ] {ℕ.𝟎}    = [≡]-intro
[−][−ₙ] {ℕ.𝐒(_)} = [≡]-intro



instance
  [+ₙ]-injectivity : Injective(+ₙ_)
  Injective.proof [+ₙ]-injectivity [≡]-intro = [≡]-intro

instance
  [−𝐒ₙ]-injectivity : Injective(−𝐒ₙ_)
  Injective.proof [−𝐒ₙ]-injectivity [≡]-intro = [≡]-intro

instance
  [−ₙ]-injectivity : Injective(−ₙ_)
  Injective.proof [−ₙ]-injectivity {ℕ.𝟎}   {ℕ.𝟎}    xy        = [≡]-intro
  Injective.proof [−ₙ]-injectivity {ℕ.𝐒 x} {ℕ.𝐒 .x} [≡]-intro = [≡]-intro

instance
  [+𝐒ₙ]-injectivity : Injective(+𝐒ₙ_)
  Injective.proof [+𝐒ₙ]-injectivity [≡]-intro = [≡]-intro



[−ₙ]-self : ∀{x} → (x −ₙ x ≡ 𝟎)
[−ₙ]-self {ℕ.𝟎}    = [≡]-intro
[−ₙ]-self {ℕ.𝐒(x)} = [−ₙ]-self {x}

instance
  [+]-commutativity : Commutativity(_+_)
  [+]-commutativity = intro(\{x y} → p{x}{y}) where
    p : Names.Commutativity(_+_)
    p {+ₙ x}  {+ₙ y}  = congruence₁(+ₙ_) (commutativity(ℕ._+_) {x}{y})
    p {+ₙ _}  {−𝐒ₙ _} = [≡]-intro
    p {−𝐒ₙ _} {+ₙ _}  = [≡]-intro
    p {−𝐒ₙ x} {−𝐒ₙ y} = congruence₁(−𝐒ₙ_ ∘ ℕ.𝐒) (commutativity(ℕ._+_) {x}{y})

instance
  [+]-identityₗ : Identityₗ(_+_)(𝟎)
  Identityₗ.proof [+]-identityₗ {+ₙ _}  = [≡]-intro
  Identityₗ.proof [+]-identityₗ {−𝐒ₙ _} = [≡]-intro

instance
  [+]-identityᵣ : Identityᵣ(_+_)(𝟎)
  Identityᵣ.proof [+]-identityᵣ {+ₙ _}  = [≡]-intro
  Identityᵣ.proof [+]-identityᵣ {−𝐒ₙ _} = [≡]-intro

instance
  [+]-identity : Identity(_+_)(𝟎)
  [+]-identity = intro

instance
  [+]-inverseFunctionₗ : InverseFunctionₗ(_+_)(−_)
  InverseFunctionₗ.proof [+]-inverseFunctionₗ {+ₙ ℕ.𝟎}    = [≡]-intro
  InverseFunctionₗ.proof [+]-inverseFunctionₗ {+ₙ ℕ.𝐒(x)} = [−ₙ]-self {x}
  InverseFunctionₗ.proof [+]-inverseFunctionₗ {−𝐒ₙ(x)}    = [−ₙ]-self {x}

instance
  [+]-inverseFunctionᵣ : InverseFunctionᵣ(_+_)(−_)
  InverseFunctionᵣ.proof [+]-inverseFunctionᵣ {+ₙ ℕ.𝟎}    = [≡]-intro
  InverseFunctionᵣ.proof [+]-inverseFunctionᵣ {+ₙ ℕ.𝐒(x)} = [−ₙ]-self {x}
  InverseFunctionᵣ.proof [+]-inverseFunctionᵣ {−𝐒ₙ(x)}    = [−ₙ]-self {x}

instance
  [+]-inverseFunction : InverseFunction(_+_)(−_)
  [+]-inverseFunction = intro


instance
  [−]-involution : Involution(−_)
  Involution.proof [−]-involution {+ₙ ℕ.𝟎}    = [≡]-intro
  Involution.proof [−]-involution {+ₙ ℕ.𝐒(x)} = [≡]-intro
  Involution.proof [−]-involution {−𝐒ₙ x}     = [≡]-intro

instance
  [−]-injectivity : Injective(−_)
  Injective.proof [−]-injectivity {a}{b} p =
    a      🝖[ _≡_ ]-[ involution(−_) ]-sym
    −(− a) 🝖[ _≡_ ]-[ congruence₁(−_) p ]
    −(− b) 🝖[ _≡_ ]-[ involution(−_) ]
    b      🝖-end

instance
  [−]-surjectivity : Surjective(−_)
  Surjective.proof [−]-surjectivity {y} = [∃]-intro (− y) ⦃ involution(−_) ⦄

instance
  [−]-bijectivity : Bijective(−_)
  [−]-bijectivity = injective-surjective-to-bijective(−_)



instance
  abs-idempotent : Idempotent(abs)
  Idempotent.proof abs-idempotent {+ₙ x}  = [≡]-intro
  Idempotent.proof abs-idempotent {−𝐒ₙ x} = [≡]-intro

abs-injective-zero : ∀{n} → (abs(n) ≡ 𝟎) → (n ≡ 𝟎)
abs-injective-zero {𝟎} [≡]-intro = [≡]-intro

abs-[−] : ∀{n} → (abs(− n) ≡ abs(n))
abs-[−] {𝟎}      = [≡]-intro
abs-[−] {+𝐒ₙ(_)} = [≡]-intro
abs-[−] {−𝐒ₙ(_)} = [≡]-intro

abs-preserving : ∀{x} → (abs(x) ≡ +ₙ(absₙ(x)))
abs-preserving {𝟎}      = [≡]-intro
abs-preserving {+𝐒ₙ(_)} = [≡]-intro
abs-preserving {−𝐒ₙ(_)} = [≡]-intro



absₙ-zero : ∀{n} → (absₙ(n) ≡ ℕ.𝟎) → (n ≡ 𝟎)
absₙ-zero {𝟎}      ([≡]-intro) = [≡]-intro




[+][𝐒]-stepₗ : ∀{x y} → (𝐒(x) + y ≡ 𝐒(x + y))
[+][𝐒]-stepₗ {+ₙ x}       {+ₙ y}       = [≡]-intro
[+][𝐒]-stepₗ {+ₙ ℕ.𝟎   }  {−𝐒ₙ ℕ.𝟎   } = [≡]-intro
[+][𝐒]-stepₗ {+ₙ ℕ.𝟎   }  {−𝐒ₙ ℕ.𝐒(_)} = [≡]-intro
[+][𝐒]-stepₗ {+ₙ ℕ.𝐒(_)}  {−𝐒ₙ ℕ.𝟎   } = [≡]-intro
[+][𝐒]-stepₗ {+ₙ ℕ.𝐒(x)}  {−𝐒ₙ ℕ.𝐒(y)} = [−ₙ][𝐒]-step{x}{ℕ.𝐒(y)}
[+][𝐒]-stepₗ {−𝐒ₙ ℕ.𝟎   } {+ₙ ℕ.𝟎   }  = [≡]-intro
[+][𝐒]-stepₗ {−𝐒ₙ ℕ.𝐒(_)} {+ₙ ℕ.𝟎   }  = [≡]-intro
[+][𝐒]-stepₗ {−𝐒ₙ ℕ.𝟎   } {+ₙ ℕ.𝐒(_)}  = [≡]-intro
[+][𝐒]-stepₗ {−𝐒ₙ ℕ.𝐒(y)} {+ₙ ℕ.𝐒(x)}  = [−ₙ][𝐒]-step{x}{ℕ.𝐒(y)}
[+][𝐒]-stepₗ {−𝐒ₙ ℕ.𝟎   } {−𝐒ₙ ℕ.𝟎   } = [≡]-intro
[+][𝐒]-stepₗ {−𝐒ₙ ℕ.𝐒(_)} {−𝐒ₙ ℕ.𝟎   } = [≡]-intro
[+][𝐒]-stepₗ {−𝐒ₙ ℕ.𝟎   } {−𝐒ₙ ℕ.𝐒(_)} = [≡]-intro
[+][𝐒]-stepₗ {−𝐒ₙ ℕ.𝐒(y)} {−𝐒ₙ ℕ.𝐒(x)} = [≡]-intro

instance
  [𝐒]-preserving-[+]ₗ : ∀{y} → Preserving₁(𝐒) (_+ y)(_+ y)
  Preserving.proof ([𝐒]-preserving-[+]ₗ {y}) {x} = symmetry(_≡_) ([+][𝐒]-stepₗ {x}{y})

[+][𝐒]-stepᵣ : ∀{x y} → (x + 𝐒(y) ≡ 𝐒(x + y))
[+][𝐒]-stepᵣ {+ₙ x}      {+ₙ y}     = [≡]-intro
[+][𝐒]-stepᵣ {+ₙ ℕ.𝟎}    {−𝐒ₙ ℕ.𝟎}   = [≡]-intro
[+][𝐒]-stepᵣ {+ₙ ℕ.𝟎}    {−𝐒ₙ ℕ.𝐒 x} = [≡]-intro
[+][𝐒]-stepᵣ {+ₙ ℕ.𝐒 x}  {−𝐒ₙ ℕ.𝟎}   = [≡]-intro
[+][𝐒]-stepᵣ {+ₙ ℕ.𝐒 x}  {−𝐒ₙ ℕ.𝐒 y} = [+][𝐒]-stepᵣ {−𝐒ₙ y}{+ₙ x}
[+][𝐒]-stepᵣ {−𝐒ₙ ℕ.𝟎}   {+ₙ ℕ.𝟎}    = [≡]-intro
[+][𝐒]-stepᵣ {−𝐒ₙ ℕ.𝟎}   {+ₙ ℕ.𝐒 y}  = [≡]-intro
[+][𝐒]-stepᵣ {−𝐒ₙ ℕ.𝐒 x} {+ₙ ℕ.𝟎}    = [≡]-intro
[+][𝐒]-stepᵣ {−𝐒ₙ ℕ.𝐒 x} {+ₙ ℕ.𝐒 y}  = [+][𝐒]-stepᵣ {−𝐒ₙ x}{+ₙ y}
[+][𝐒]-stepᵣ {−𝐒ₙ ℕ.𝟎}   {−𝐒ₙ ℕ.𝟎}   = [≡]-intro
[+][𝐒]-stepᵣ {−𝐒ₙ ℕ.𝐒 x} {−𝐒ₙ ℕ.𝟎}   = [≡]-intro
[+][𝐒]-stepᵣ {−𝐒ₙ ℕ.𝟎}   {−𝐒ₙ ℕ.𝐒 y} = [≡]-intro
[+][𝐒]-stepᵣ {−𝐒ₙ ℕ.𝐒 x} {−𝐒ₙ ℕ.𝐒 y} = [≡]-intro

instance
  [𝐒]-preserving-[+]ᵣ : ∀{x} → Preserving₁(𝐒) (_+_ x)(_+_ x)
  Preserving.proof ([𝐒]-preserving-[+]ᵣ {x}) {y} = symmetry(_≡_) ([+][𝐒]-stepᵣ {x}{y})

[+][𝐏]-stepₗ : ∀{x y} → (𝐏(x) + y ≡ 𝐏(x + y))
[+][𝐏]-stepₗ {x}{y} =
  𝐏(x) + y                 🝖[ _≡_ ]-[ congruence₂(_+_) (congruence₁(𝐏) (involution(−_) {x})) (involution(−_) {y}) ]-sym
  𝐏(−(− x)) + (−(− y))     🝖[ _≡_ ]-[ congruence₂ₗ(_+_)(−(− y)) (preserving₁(−_)(𝐒)(𝐏) {− x}) ]-sym
  (− 𝐒(− x)) + (−(− y))    🝖[ _≡_ ]-[ preserving₂(−_)(_+_)(_+_) {𝐒(− x)}{− y} ]-sym
  −(𝐒(− x) + (− y))        🝖[ _≡_ ]-[ congruence₁(−_) ([+][𝐒]-stepₗ {− x}{− y}) ]
  −(𝐒((− x) + (− y)))      🝖[ _≡_ ]-[ preserving₁(−_)(𝐒)(𝐏) ]
  𝐏(−((− x) + (− y)))      🝖[ _≡_ ]-[ congruence₁(𝐏) (preserving₂(−_)(_+_)(_+_) {− x}{− y}) ]
  𝐏(((−(− x)) + (−(− y)))) 🝖[ _≡_ ]-[ congruence₁(𝐏) (congruence₂(_+_) (involution(−_) {x}) (involution(−_) {y})) ]
  𝐏(x + y)                 🝖-end

instance
  [𝐏]-preserving-[+]ₗ : ∀{y} → Preserving₁(𝐏) (_+ y)(_+ y)
  Preserving.proof ([𝐏]-preserving-[+]ₗ {y}) {x} = symmetry(_≡_) ([+][𝐏]-stepₗ {x}{y})

[+][𝐏]-stepᵣ : ∀{x y} → (x + 𝐏(y) ≡ 𝐏(x + y))
[+][𝐏]-stepᵣ {x}{y} =
  x + 𝐏(y)                 🝖[ _≡_ ]-[ congruence₂(_+_) (involution(−_) {x}) (congruence₁(𝐏) (involution(−_) {y})) ]-sym
  (−(− x)) + 𝐏(−(− y))     🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(−(− x)) (preserving₁(−_)(𝐒)(𝐏) {− y}) ]-sym
  (−(− x)) + (− 𝐒(− y))    🝖[ _≡_ ]-[ preserving₂(−_)(_+_)(_+_) {− x}{𝐒(− y)} ]-sym
  −((− x) + 𝐒(− y))        🝖[ _≡_ ]-[ congruence₁(−_) ([+][𝐒]-stepᵣ {− x}{− y}) ]
  −(𝐒((− x) + (− y)))      🝖[ _≡_ ]-[ preserving₁(−_)(𝐒)(𝐏) ]
  𝐏(−((− x) + (− y)))      🝖[ _≡_ ]-[ congruence₁(𝐏) (preserving₂(−_)(_+_)(_+_) {− x}{− y}) ]
  𝐏(((−(− x)) + (−(− y)))) 🝖[ _≡_ ]-[ congruence₁(𝐏) (congruence₂(_+_) (involution(−_) {x}) (involution(−_) {y})) ]
  𝐏(x + y)                 🝖-end

instance
  [𝐏]-preserving-[+]ᵣ : ∀{x} → Preserving₁(𝐏) (_+_ x)(_+_ x)
  Preserving.proof ([𝐏]-preserving-[+]ᵣ {x}) {y} = symmetry(_≡_) ([+][𝐏]-stepᵣ {x}{y})



instance
  [+]-associativity : Associativity(_+_)
  [+]-associativity = intro(\{x y z} → p{x}{y}{z}) where
    postulate p : Names.Associativity(_+_)
    {-p {x} {y} {𝟎}     =
      (x + y) + 𝟎 🝖[ _≡_ ]-[ identityᵣ(_+_)(𝟎) ]
      x + y       🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x) (identityᵣ(_+_)(𝟎)) ]-sym
      x + (y + 𝟎) 🝖-end
    p {x} {y} {+𝐒ₙ z} =
      (x + y) + (+𝐒ₙ(z))   🝖[ _≡_ ]-[]
      (x + y) + 𝐒(+ₙ(z))   🝖[ _≡_ ]-[ [+][𝐒]-stepᵣ {x + y}{+ₙ(z)} ]
      𝐒((x + y) + (+ₙ(z))) 🝖[ _≡_ ]-[ congruence₁(𝐒) (p{x}{y}{+ₙ z}) ]
      𝐒(x + (y + (+ₙ(z)))) 🝖[ _≡_ ]-[ [+][𝐒]-stepᵣ {x}{y + (+ₙ z)} ]-sym
      x + 𝐒(y + (+ₙ(z)))   🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x) ([+][𝐒]-stepᵣ {y}{+ₙ z}) ]-sym
      x + (y + 𝐒(+ₙ(z)))   🝖[ _≡_ ]-[]
      x + (y + (+𝐒ₙ(z)))   🝖-end
    p {x} {y} {−𝐒ₙ z} =
      (x + y) + (−𝐒ₙ(z))   🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x + y) [𝐏]-negative ]-sym
      (x + y) + 𝐏(−ₙ(z))   🝖[ _≡_ ]-[ [+][𝐏]-stepᵣ {x + y}{−ₙ(z)} ]
      𝐏((x + y) + (−ₙ(z))) 🝖[ _≡_ ]-[ congruence₁(𝐏) (p{x}{y}{−ₙ z}) ]
      𝐏(x + (y + (−ₙ(z)))) 🝖[ _≡_ ]-[ [+][𝐏]-stepᵣ {x}{y + (−ₙ z)} ]-sym
      x + 𝐏(y + (−ₙ(z)))   🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x) ([+][𝐏]-stepᵣ {y}{−ₙ z}) ]-sym
      x + (y + 𝐏(−ₙ(z)))   🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x) (congruence₂ᵣ(_+_)(y) [𝐏]-negative) ]
      x + (y + (−𝐒ₙ(z)))   🝖-end
    -}

instance
  [+]-monoid : Monoid(_+_)
  [+]-monoid = intro

instance
  [+]-group : Group(_+_)
  [+]-group = intro

instance
  [+]-commutative-group : CommutativeGroup(_+_)
  [+]-commutative-group = intro

absₙ-of-[⋅] : ∀{x y} → (absₙ(x ⋅ y) ≡ absₙ(x) ℕ.⋅ absₙ(y))
absₙ-of-[⋅] {+ₙ ℕ.𝟎}    {+ₙ ℕ.𝟎}    = [≡]-intro
absₙ-of-[⋅] {+ₙ ℕ.𝟎}    {+ₙ ℕ.𝐒 y}  = [≡]-intro
absₙ-of-[⋅] {+ₙ ℕ.𝐒 x}  {+ₙ ℕ.𝟎}    = [≡]-intro
absₙ-of-[⋅] {+ₙ ℕ.𝐒 x}  {+ₙ ℕ.𝐒 y}  = [≡]-intro
absₙ-of-[⋅] {−𝐒ₙ x}     {−𝐒ₙ y}     = [≡]-intro
absₙ-of-[⋅] {+ₙ ℕ.𝟎}    {−𝐒ₙ ℕ.𝟎}   = [≡]-intro
absₙ-of-[⋅] {+ₙ ℕ.𝟎}    {−𝐒ₙ ℕ.𝐒 y} = [≡]-intro
absₙ-of-[⋅] {+ₙ ℕ.𝐒 x}  {−𝐒ₙ ℕ.𝟎}   = [≡]-intro
absₙ-of-[⋅] {+ₙ ℕ.𝐒 x}  {−𝐒ₙ ℕ.𝐒 y} = [≡]-intro
absₙ-of-[⋅] {−𝐒ₙ ℕ.𝟎}   {+ₙ ℕ.𝟎}    = [≡]-intro
absₙ-of-[⋅] {−𝐒ₙ ℕ.𝟎}   {+ₙ ℕ.𝐒 y}  = [≡]-intro
absₙ-of-[⋅] {−𝐒ₙ ℕ.𝐒 x} {+ₙ ℕ.𝟎}    = [≡]-intro
absₙ-of-[⋅] {−𝐒ₙ ℕ.𝐒 x} {+ₙ ℕ.𝐒 y}  = [≡]-intro

sign-of-[⋅] : ∀{x y} → (sign0(x ⋅ y) ≡ sign0(x) Sign.⨯ sign0(y))
sign-of-[⋅] {+ₙ ℕ.𝟎}    {+ₙ ℕ.𝟎}    = [≡]-intro
sign-of-[⋅] {+ₙ ℕ.𝟎}    {+ₙ ℕ.𝐒 y}  = [≡]-intro
sign-of-[⋅] {+ₙ ℕ.𝐒 x}  {+ₙ ℕ.𝟎}    = [≡]-intro
sign-of-[⋅] {+ₙ ℕ.𝐒 x}  {+ₙ ℕ.𝐒 y}  = [≡]-intro
sign-of-[⋅] {−𝐒ₙ x}     {−𝐒ₙ y}     = [≡]-intro
sign-of-[⋅] {+ₙ ℕ.𝟎}    {−𝐒ₙ ℕ.𝟎}   = [≡]-intro
sign-of-[⋅] {+ₙ ℕ.𝟎}    {−𝐒ₙ ℕ.𝐒 y} = [≡]-intro
sign-of-[⋅] {+ₙ ℕ.𝐒 x}  {−𝐒ₙ ℕ.𝟎}   = [≡]-intro
sign-of-[⋅] {+ₙ ℕ.𝐒 x}  {−𝐒ₙ ℕ.𝐒 y} = [≡]-intro
sign-of-[⋅] {−𝐒ₙ ℕ.𝟎}   {+ₙ ℕ.𝟎}    = [≡]-intro
sign-of-[⋅] {−𝐒ₙ ℕ.𝟎}   {+ₙ ℕ.𝐒 y}  = [≡]-intro
sign-of-[⋅] {−𝐒ₙ ℕ.𝐒 x} {+ₙ ℕ.𝟎}    = [≡]-intro
sign-of-[⋅] {−𝐒ₙ ℕ.𝐒 x} {+ₙ ℕ.𝐒 y}  = [≡]-intro

signed-inverse : ∀{x} → (signedℕ (sign0 x) (absₙ x) ≡ x)
signed-inverse {+𝐒ₙ _} = [≡]-intro
signed-inverse {𝟎}     = [≡]-intro
signed-inverse {−𝐒ₙ _} = [≡]-intro

sign0-inverse : ∀{x}{y} → (sign0(signedℕ x (ℕ.𝐒(y))) ≡ x)
sign0-inverse {Sign.➕} {y} = [≡]-intro
sign0-inverse {Sign.𝟎}  {y} = [≡]-intro
sign0-inverse {Sign.➖} {y} = [≡]-intro

absₙ-inverse : ∀{x}{y} → (x ≢ Sign.𝟎) → (absₙ(signedℕ x y) ≡ y)
absₙ-inverse {Sign.➕} {ℕ.𝟎}   _ = [≡]-intro
absₙ-inverse {Sign.➕} {ℕ.𝐒 y} _ = [≡]-intro
absₙ-inverse {Sign.➖} {ℕ.𝟎}   _ = [≡]-intro
absₙ-inverse {Sign.➖} {ℕ.𝐒 y} _ = [≡]-intro
absₙ-inverse {Sign.𝟎} {ℕ.𝟎}    _ = [≡]-intro
absₙ-inverse {Sign.𝟎} {ℕ.𝐒 y}  p with () ← p [≡]-intro

[⋅]-equality : ∀{x y z} → (x ⋅ y ≡ z) ↔ (sign0(x) Sign.⨯ sign0(y) ≡ sign0 z) ∧ (absₙ(x) ℕ.⋅ absₙ(y) ≡ absₙ(z))
[⋅]-equality {x}{y}{z} = [↔]-intro (Tuple.uncurry l) r where
  l : ∀{x y z} → (sign0(x) Sign.⨯ sign0(y) ≡ sign0 z) → (absₙ(x) ℕ.⋅ absₙ(y) ≡ absₙ(z)) → (x ⋅ y ≡ z)
  l{x}{y}{z} p q = congruence₂(signedℕ) p q 🝖 signed-inverse

  r : ∀{x y z} → (x ⋅ y ≡ z) → (sign0(x) Sign.⨯ sign0(y) ≡ sign0 z) ∧ (absₙ(x) ℕ.⋅ absₙ(y) ≡ absₙ(z))
  r{x}{y}{z} p = [∧]-intro (symmetry(_≡_) sign-of-[⋅] 🝖 congruence₁(sign0) p) (symmetry(_≡_) (absₙ-of-[⋅] {x}{y}) 🝖 congruence₁(absₙ) p)

instance
  [⋅]-identityₗ : Identityₗ(_⋅_)(𝟏)
  Identityₗ.proof [⋅]-identityₗ {x} with sign0 x | x
  ... | Sign.➕ | 𝟎     = [≡]-intro
  ... | Sign.➕ | +𝐒ₙ _ = [≡]-intro
  ... | Sign.➕ | −𝐒ₙ _ = [≡]-intro
  ... | Sign.𝟎 | 𝟎     = [≡]-intro
  ... | Sign.𝟎 | +𝐒ₙ _ = [≡]-intro
  ... | Sign.𝟎 | −𝐒ₙ _ = [≡]-intro
  ... | Sign.➖ | 𝟎     = [≡]-intro
  ... | Sign.➖ | +𝐒ₙ _ = [≡]-intro
  ... | Sign.➖ | −𝐒ₙ _ = [≡]-intro

instance
  [⋅]-identityᵣ : Identityᵣ(_⋅_)(𝟏)
  Identityᵣ.proof [⋅]-identityᵣ {x} with sign0 x | x
  ... | Sign.➕ | 𝟎     = [≡]-intro
  ... | Sign.➕ | +𝐒ₙ _ = [≡]-intro
  ... | Sign.➕ | −𝐒ₙ _ = [≡]-intro
  ... | Sign.𝟎 | 𝟎     = [≡]-intro
  ... | Sign.𝟎 | +𝐒ₙ _ = [≡]-intro
  ... | Sign.𝟎 | −𝐒ₙ _ = [≡]-intro
  ... | Sign.➖ | 𝟎     = [≡]-intro
  ... | Sign.➖ | +𝐒ₙ _ = [≡]-intro
  ... | Sign.➖ | −𝐒ₙ _ = [≡]-intro

instance
  [⋅]-commutativity : Commutativity(_⋅_)
  Commutativity.proof [⋅]-commutativity {x}{y} = congruence₂(signedℕ) (commutativity(Sign._⨯_)) (commutativity(ℕ._⋅_) {absₙ x}{absₙ y})

instance
  postulate [⋅]-associativity : Associativity(_⋅_)
  {-Associativity.proof [⋅]-associativity {x}{y}{z} =
    congruence₂(signedℕ)
      (congruence₂ₗ(Sign._⨯_)(sign0 z) sign0-inverse                                                  🝖 associativity(Sign._⨯_)                      🝖 symmetry(_≡_) (congruence₂ᵣ(Sign._⨯_)(sign0(x)) (sign-of-[⋅] {y}{z})))
      (congruence₂ₗ(ℕ._⋅_)   (absₙ(z)) (absₙ-inverse{sign0(x) Sign.⨯ sign0(y)}{absₙ(x) ℕ.⋅ absₙ(y)})  🝖 associativity(ℕ._⋅_){absₙ x}{absₙ y}{absₙ z} 🝖 symmetry(_≡_) (congruence₂ᵣ(ℕ._⋅_)   (absₙ (x)) (absₙ-of-[⋅] {y}{z})))
  -}

instance
  postulate [⋅][+]-distributivityₗ : Distributivityₗ(_⋅_)(_+_)
  {-[⋅][+]-distributivityₗ = intro p where
    p : Names.Distributivityₗ(_⋅_)(_+_)
    p {+ₙ ℕ.𝟎} {+ₙ ℕ.𝟎} {+ₙ ℕ.𝟎} = [≡]-intro
    p {+ₙ ℕ.𝟎} {+ₙ ℕ.𝟎} {+ₙ ℕ.𝐒 z} = [≡]-intro
    p {+ₙ ℕ.𝟎} {+ₙ ℕ.𝐒 y} {+ₙ ℕ.𝟎} = [≡]-intro
    p {+ₙ ℕ.𝟎} {+ₙ ℕ.𝐒 y} {+ₙ ℕ.𝐒 z} = [≡]-intro
    p {+ₙ ℕ.𝐒 x} {+ₙ ℕ.𝟎} {+ₙ ℕ.𝟎} = [≡]-intro
    p {+ₙ ℕ.𝐒 x} {+ₙ ℕ.𝟎} {+ₙ ℕ.𝐒 z} = [≡]-intro
    p {+ₙ ℕ.𝐒 x} {+ₙ ℕ.𝐒 y} {+ₙ ℕ.𝟎} = [≡]-intro
    p {+ₙ ℕ.𝐒 x} {+ₙ ℕ.𝐒 y} {+ₙ ℕ.𝐒 z} = {!!}
    p {+ₙ ℕ.𝟎} {+ₙ ℕ.𝟎} {−𝐒ₙ z} = [≡]-intro
    p {+ₙ ℕ.𝟎} {+ₙ ℕ.𝐒 y} {−𝐒ₙ z} = {!!}
    p {+ₙ ℕ.𝐒 x} {+ₙ ℕ.𝟎} {−𝐒ₙ z} = [≡]-intro
    p {+ₙ ℕ.𝐒 x} {+ₙ ℕ.𝐒 y} {−𝐒ₙ z} = {!!}
    p {+ₙ ℕ.𝟎} {−𝐒ₙ y} {+ₙ ℕ.𝟎} = [≡]-intro
    p {+ₙ ℕ.𝟎} {−𝐒ₙ y} {+ₙ ℕ.𝐒 z} = {!!}
    p {+ₙ ℕ.𝐒 x} {−𝐒ₙ y} {+ₙ ℕ.𝟎} = [≡]-intro
    p {+ₙ ℕ.𝐒 x} {−𝐒ₙ y} {+ₙ ℕ.𝐒 z} = {!!}
    p {+ₙ ℕ.𝟎} {−𝐒ₙ y} {−𝐒ₙ z} = [≡]-intro
    p {+ₙ ℕ.𝐒 x} {−𝐒ₙ y} {−𝐒ₙ z} = {!!}
    p {−𝐒ₙ x} {+ₙ ℕ.𝟎} {+ₙ ℕ.𝟎} = [≡]-intro
    p {−𝐒ₙ x} {+ₙ ℕ.𝟎} {+ₙ ℕ.𝐒 z} = [≡]-intro
    p {−𝐒ₙ x} {+ₙ ℕ.𝐒 y} {+ₙ ℕ.𝟎} = [≡]-intro
    p {−𝐒ₙ x} {+ₙ ℕ.𝐒 y} {+ₙ ℕ.𝐒 z} = {!!}
    p {−𝐒ₙ x} {+ₙ ℕ.𝟎} {−𝐒ₙ z} = [≡]-intro
    p {−𝐒ₙ x} {+ₙ ℕ.𝐒 y} {−𝐒ₙ z} = {!!}
    p {−𝐒ₙ x} {−𝐒ₙ y} {+ₙ ℕ.𝟎} = [≡]-intro
    p {−𝐒ₙ x} {−𝐒ₙ y} {+ₙ ℕ.𝐒 z} = {!!}
    p {−𝐒ₙ x} {−𝐒ₙ y} {−𝐒ₙ z} = {!!}-}
  {-
    x ⋅ (y + z)                                                                                                                     🝖[ _≡_ ]-[]
    signedℕ ((sign0 x) Sign.⨯ (sign0(y + z))) ((absₙ x) ℕ.⋅ (absₙ(y + z)))                                                          🝖[ _≡_ ]-[ {!congruence₂(signedℕ) ? ?!} ]
    signedℕ ((sign0 x) Sign.⨯ sign0(y + z)) ((absₙ x) ℕ.⋅ (absₙ(y + z)))                                                          🝖[ _≡_ ]-[ {!!} ]
    (signedℕ ((sign0 x) Sign.⨯ (sign0 y)) ((absₙ x) ℕ.⋅ (absₙ y))) + (signedℕ ((sign0 x) Sign.⨯ (sign0 z)) ((absₙ x) ℕ.⋅ (absₙ z))) 🝖[ _≡_ ]-[]
    (x ⋅ y) + (x ⋅ z)                                                                                                               🝖-end
    where
      sign0-proof : ∀{x y z} → ((sign0 x) Sign.⨯ sign0(y + z) ≡ (sign0(x) + sign0(z)) Sign.⨯ (sign0(x) + sign0(z)))
  -}

instance
  postulate [⋅][+]-distributivityᵣ : Distributivityᵣ(_⋅_)(_+_)

instance
  [+][⋅]-rng : Rng(_+_)(_⋅_)
  [+][⋅]-rng = record{}

instance
  [+][⋅]-ring-unity : Unity(_+_)(_⋅_)
  Unity.[⋅]-identity-existence [+][⋅]-ring-unity = [∃]-intro 𝟏 ⦃ intro ⦄
    
instance
  [+][⋅]-ring : Ring(_+_)(_⋅_)
  [+][⋅]-ring = record{}
  
import      Numeral.Natural.Relation.Order as ℕ
import      Numeral.Natural.Relation.Order.Proofs as ℕ
import      Structure.Relator.Ordering as Structure
data _≤_ : ℤ → ℤ → Type{Lvl.𝟎} where
  pos : ∀{a b} → (a ℕ.≤ b) → ((+ₙ a) ≤ (+ₙ b))
  neg : ∀{a b} → (a ℕ.≥ b) → ((−𝐒ₙ a) ≤ (−𝐒ₙ b))
  mix : ∀{a b} → ((−𝐒ₙ a) ≤ (+ₙ b))

instance
  [≤]-reflexivity : Reflexivity(_≤_)
  Reflexivity.proof [≤]-reflexivity {+ₙ  x} = pos (reflexivity(ℕ._≤_))
  Reflexivity.proof [≤]-reflexivity {−𝐒ₙ x} = neg (reflexivity(ℕ._≤_))

instance
  [≤]-transitivity : Transitivity(_≤_)
  Transitivity.proof [≤]-transitivity (pos p) (pos q) = pos(transitivity(ℕ._≤_) p q)
  Transitivity.proof [≤]-transitivity (neg p) (neg q) = neg(transitivity(ℕ._≤_) q p)
  Transitivity.proof [≤]-transitivity (neg p) mix     = mix
  Transitivity.proof [≤]-transitivity mix     (pos q) = mix

instance
  [≤]-antisymmetry : Antisymmetry(_≤_)(_≡_)
  Antisymmetry.proof [≤]-antisymmetry (pos {ℕ.𝟎}   {ℕ.𝟎}   p) (pos q) = [≡]-intro
  Antisymmetry.proof [≤]-antisymmetry (neg {ℕ.𝟎}   {ℕ.𝟎}   p) (neg q) = [≡]-intro
  Antisymmetry.proof [≤]-antisymmetry (pos {ℕ.𝐒 a} {ℕ.𝐒 b} p) (pos q) = congruence₁(+ₙ_)  (antisymmetry(ℕ._≤_)(_≡_) p q)
  Antisymmetry.proof [≤]-antisymmetry (neg {ℕ.𝐒 a} {ℕ.𝐒 b} p) (neg q) = congruence₁(−𝐒ₙ_) (antisymmetry(ℕ._≤_)(_≡_) q p)

instance
  [≤]-converseTotal : ConverseTotal(_≤_)
  ConverseTotal.proof [≤]-converseTotal {+ₙ  x} {+ₙ  y} = Either.map2 pos pos (converseTotal(ℕ._≤_))
  ConverseTotal.proof [≤]-converseTotal {+ₙ  x} {−𝐒ₙ y} = Either.Right mix
  ConverseTotal.proof [≤]-converseTotal {−𝐒ₙ x} {+ₙ  y} = Either.Left  mix
  ConverseTotal.proof [≤]-converseTotal {−𝐒ₙ x} {−𝐒ₙ y} = Either.map2 neg neg (converseTotal(ℕ._≤_))


instance
  [≤]-weakPartialOrder : Structure.Weak.PartialOrder(_≤_)(_≡_)
  [≤]-weakPartialOrder = record{}

instance
  [≤]-totalOrder : Structure.Weak.TotalOrder(_≤_)(_≡_)
  [≤]-totalOrder = record{}

instance
  [+][⋅][≤]-orderedRing : Ordered(_+_)(_⋅_)(_≤_)
  Ordered.[≤][+]ₗ-preserve  [+][⋅][≤]-orderedRing = p where
    postulate p : ∀{x y z} → (x ≤ y) → ((x + z) ≤ (y + z))
    {-p {+ₙ x}    {+ₙ y}     {+ₙ  z} (pos xy) = pos {!!}
    p {−𝐒ₙ x}   {−𝐒ₙ y}    {−𝐒ₙ z} (neg xy) = neg {!!}
    p {+ₙ ℕ.𝟎}  {+ₙ ℕ.𝟎}   {−𝐒ₙ z} (pos xy) = reflexivity(_≤_)
    p {+ₙ ℕ.𝟎}  {+ₙ ℕ.𝐒 y} {−𝐒ₙ z} (pos xy) = {!!}
    p {+ₙ ℕ.𝐒 x} {+ₙ ℕ.𝐒 y}{−𝐒ₙ z} (pos xy) = {!!}
    p {.(−𝐒ₙ _)} {.(+ₙ _)} {+ₙ  z} mix = {!!}
    p {.(−𝐒ₙ _)} {.(+ₙ _)} {−𝐒ₙ z} mix = {!!}-}
  Ordered.[≤][⋅]-zero       [+][⋅][≤]-orderedRing = p where
    p : ∀{x y} → (𝟎 ≤ x) → (𝟎 ≤ y) → (𝟎 ≤ (x ⋅ y))
    p {+ₙ ℕ.𝟎}   {+ₙ ℕ.𝟎}   (pos px) (pos py) = pos py
    p {+ₙ ℕ.𝟎}   {+ₙ ℕ.𝐒 y} (pos px) (pos py) = pos px
    p {+ₙ ℕ.𝐒 x} {+ₙ ℕ.𝟎}   (pos px) (pos py) = pos py
    p {+ₙ ℕ.𝐒 x} {+ₙ ℕ.𝐒 y} (pos px) (pos py) = pos ℕ.[≤]-minimum
