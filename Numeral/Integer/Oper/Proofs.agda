module Numeral.Integer.Oper.Proofs where

import      Data.Either as Either
open import Data.Tuple  as Tuple using (_,_)
open import Logic
import      Lvl
open import Functional hiding (_∘_ ; _∘₂_)
open import Functional.Dependent using (_∘_ ; _∘₂_)
open import Numeral.Integer
open import Numeral.Integer.Construction
open import Numeral.Integer.Construction.Proofs
open import Numeral.Integer.Function hiding (+_)
open import Numeral.Integer.Induction
open import Numeral.Integer.Oper
open import Numeral.Integer.Relation
open import Numeral.Integer.Proofs
open import Numeral.Integer.Sign
open import Numeral.Natural as ℕ using (ℕ)
import      Numeral.Natural.Oper as ℕ
import      Numeral.Natural.Oper.Proofs as ℕ
import      Numeral.Natural.Oper.Proofs.Structure as ℕ
import      Numeral.Natural.Relation.Order as ℕ
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
open import Structure.Operator.Semi
open import Structure.OrderedField
open import Structure.Relator.Properties
open import Syntax.Number
open import Syntax.Transitivity
open import Type

private variable ℓ : Lvl.Level

instance
  [+ₙ][𝐒]-preserving : Preserving₁(+ₙ_) ℕ.𝐒 𝐒
  [+ₙ][𝐒]-preserving = intro [≡]-intro

instance
  [−ₙ][𝐒][𝐏]-preserving : Preserving₁(−ₙ_) ℕ.𝐒 𝐏
  Preserving.proof [−ₙ][𝐒][𝐏]-preserving {ℕ.𝟎}   = [≡]-intro
  Preserving.proof [−ₙ][𝐒][𝐏]-preserving {ℕ.𝐒 x} = [≡]-intro

instance
  [+ₙ][+]-preserving : Preserving₂(+ₙ_) (ℕ._+_)(_+_)
  [+ₙ][+]-preserving = intro [≡]-intro

instance
  [−ₙ][+]-preserving : Preserving₂(−ₙ_) (ℕ._+_)(_+_)
  Preserving.proof [−ₙ][+]-preserving {ℕ.𝟎}    {ℕ.𝟎}    = [≡]-intro
  Preserving.proof [−ₙ][+]-preserving {ℕ.𝟎}    {ℕ.𝐒(_)} = [≡]-intro
  Preserving.proof [−ₙ][+]-preserving {ℕ.𝐒(_)} {ℕ.𝟎}    = [≡]-intro
  Preserving.proof [−ₙ][+]-preserving {ℕ.𝐒(_)} {ℕ.𝐒(_)} = [≡]-intro

instance
  signed-[+]-preserving : ∀{s} → Preserving₂(signed s) (ℕ._+_)(_+_)
  signed-[+]-preserving {Sign.➕} = [+ₙ][+]-preserving
  signed-[+]-preserving {Sign.➖} = [−ₙ][+]-preserving

instance
  [+ₙ][⋅]-preserving : Preserving₂(+ₙ_) (ℕ._⋅_) (_⋅_)
  Preserving.proof [+ₙ][⋅]-preserving {ℕ.𝟎}   {ℕ.𝟎}   = [≡]-intro
  Preserving.proof [+ₙ][⋅]-preserving {ℕ.𝟎}   {ℕ.𝐒 y} = [≡]-intro
  Preserving.proof [+ₙ][⋅]-preserving {ℕ.𝐒 x} {ℕ.𝟎}   = [≡]-intro
  Preserving.proof [+ₙ][⋅]-preserving {ℕ.𝐒 x} {ℕ.𝐒 y} = [≡]-intro

-- [−₀]-preserving : Preserving₂(+ₙ_) (_−₀ₙ_) (_−₀_)
-- [/₀]-preserving : Preserving₂(+ₙ_) (_/₀ₙ_) (_/₀_)

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

instance
  [absₙ][⋅]-preserving : Preserving₂(absₙ)(_⋅_)(ℕ._⋅_)
  Preserving.proof [absₙ][⋅]-preserving {+ₙ ℕ.𝟎}    {+ₙ ℕ.𝟎}    = [≡]-intro
  Preserving.proof [absₙ][⋅]-preserving {+ₙ ℕ.𝟎}    {+ₙ ℕ.𝐒 y}  = [≡]-intro
  Preserving.proof [absₙ][⋅]-preserving {+ₙ ℕ.𝐒 x}  {+ₙ ℕ.𝟎}    = [≡]-intro
  Preserving.proof [absₙ][⋅]-preserving {+ₙ ℕ.𝐒 x}  {+ₙ ℕ.𝐒 y}  = [≡]-intro
  Preserving.proof [absₙ][⋅]-preserving {−𝐒ₙ x}     {−𝐒ₙ y}     = [≡]-intro
  Preserving.proof [absₙ][⋅]-preserving {+ₙ ℕ.𝟎}    {−𝐒ₙ ℕ.𝟎}   = [≡]-intro
  Preserving.proof [absₙ][⋅]-preserving {+ₙ ℕ.𝟎}    {−𝐒ₙ ℕ.𝐒 y} = [≡]-intro
  Preserving.proof [absₙ][⋅]-preserving {+ₙ ℕ.𝐒 x}  {−𝐒ₙ ℕ.𝟎}   = [≡]-intro
  Preserving.proof [absₙ][⋅]-preserving {+ₙ ℕ.𝐒 x}  {−𝐒ₙ ℕ.𝐒 y} = [≡]-intro
  Preserving.proof [absₙ][⋅]-preserving {−𝐒ₙ ℕ.𝟎}   {+ₙ ℕ.𝟎}    = [≡]-intro
  Preserving.proof [absₙ][⋅]-preserving {−𝐒ₙ ℕ.𝟎}   {+ₙ ℕ.𝐒 y}  = [≡]-intro
  Preserving.proof [absₙ][⋅]-preserving {−𝐒ₙ ℕ.𝐒 x} {+ₙ ℕ.𝟎}    = [≡]-intro
  Preserving.proof [absₙ][⋅]-preserving {−𝐒ₙ ℕ.𝐒 x} {+ₙ ℕ.𝐒 y}  = [≡]-intro

instance
  [sign0][⋅]-preserving : Preserving₂(sign0)(_⋅_)(Sign._⨯_)
  Preserving.proof [sign0][⋅]-preserving {+ₙ ℕ.𝟎}    {+ₙ ℕ.𝟎}    = [≡]-intro
  Preserving.proof [sign0][⋅]-preserving {+ₙ ℕ.𝟎}    {+ₙ ℕ.𝐒 y}  = [≡]-intro
  Preserving.proof [sign0][⋅]-preserving {+ₙ ℕ.𝐒 x}  {+ₙ ℕ.𝟎}    = [≡]-intro
  Preserving.proof [sign0][⋅]-preserving {+ₙ ℕ.𝐒 x}  {+ₙ ℕ.𝐒 y}  = [≡]-intro
  Preserving.proof [sign0][⋅]-preserving {−𝐒ₙ x}     {−𝐒ₙ y}     = [≡]-intro
  Preserving.proof [sign0][⋅]-preserving {+ₙ ℕ.𝟎}    {−𝐒ₙ ℕ.𝟎}   = [≡]-intro
  Preserving.proof [sign0][⋅]-preserving {+ₙ ℕ.𝟎}    {−𝐒ₙ ℕ.𝐒 y} = [≡]-intro
  Preserving.proof [sign0][⋅]-preserving {+ₙ ℕ.𝐒 x}  {−𝐒ₙ ℕ.𝟎}   = [≡]-intro
  Preserving.proof [sign0][⋅]-preserving {+ₙ ℕ.𝐒 x}  {−𝐒ₙ ℕ.𝐒 y} = [≡]-intro
  Preserving.proof [sign0][⋅]-preserving {−𝐒ₙ ℕ.𝟎}   {+ₙ ℕ.𝟎}    = [≡]-intro
  Preserving.proof [sign0][⋅]-preserving {−𝐒ₙ ℕ.𝟎}   {+ₙ ℕ.𝐒 y}  = [≡]-intro
  Preserving.proof [sign0][⋅]-preserving {−𝐒ₙ ℕ.𝐒 x} {+ₙ ℕ.𝟎}    = [≡]-intro
  Preserving.proof [sign0][⋅]-preserving {−𝐒ₙ ℕ.𝐒 x} {+ₙ ℕ.𝐒 y}  = [≡]-intro

-- (−n)−1 = −(n+1)
[𝐏]-negative : ∀{n} → (𝐏(−ₙ n) ≡ −𝐒ₙ(n))
[𝐏]-negative {ℕ.𝟎}    = [≡]-intro
[𝐏]-negative {ℕ.𝐒(n)} = [≡]-intro

-- (−(n+1))+1 = −n
[𝐒][−𝐒ₙ]-negative-identity : ∀{n} → (𝐒(−𝐒ₙ(n)) ≡ −ₙ n)
[𝐒][−𝐒ₙ]-negative-identity {ℕ.𝟎}    = [≡]-intro
[𝐒][−𝐒ₙ]-negative-identity {ℕ.𝐒(n)} = [≡]-intro

[−𝐒][−𝐒ₙ]-identity : ∀{n} → (− 𝐒(+ₙ n) ≡ −𝐒ₙ(n))
[−𝐒][−𝐒ₙ]-identity {n} = [≡]-intro



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



[−][−ₙ] : ∀{x} → (−(+ₙ x) ≡ −ₙ x)
[−][−ₙ] {ℕ.𝟎}    = [≡]-intro
[−][−ₙ] {ℕ.𝐒(_)} = [≡]-intro

[−ₙ][𝐒]-step : ∀{x y} → (ℕ.𝐒(x) −ₙ y ≡ 𝐒(x −ₙ y))
[−ₙ][𝐒]-step {ℕ.𝟎}   {ℕ.𝟎}    = [≡]-intro
[−ₙ][𝐒]-step {ℕ.𝟎}   {ℕ.𝐒(y)} = [−ₙ]-antiidentityₗ {y} 🝖 symmetry(_≡_) ([𝐒][−𝐒ₙ]-negative-identity{y})
[−ₙ][𝐒]-step {ℕ.𝐒(_)}{ℕ.𝟎}    = [≡]-intro
[−ₙ][𝐒]-step {ℕ.𝐒(x)}{ℕ.𝐒(y)} = [−ₙ][𝐒]-step {x}{y}



sign-of-signed-𝐒 : ∀{s}{n} → (sign(signed s (ℕ.𝐒(n))) ≡ s)
sign-of-signed-𝐒 {Sign.➕} = [≡]-intro
sign-of-signed-𝐒 {Sign.➖} = [≡]-intro

sign0-of-signed-𝐒 : ∀{s}{n} → (sign0(signed s (ℕ.𝐒(n))) ≡ Sign.zeroable(s))
sign0-of-signed-𝐒 {Sign.➕} = [≡]-intro
sign0-of-signed-𝐒 {Sign.➖} = [≡]-intro





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
  [𝐒]-preserving-[+]ᵣ : ∀{x} → Preserving₁(𝐒) (x +_)(x +_)
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
  [𝐏]-preserving-[+]ᵣ : ∀{x} → Preserving₁(𝐏) (x +_)(x +_)
  Preserving.proof ([𝐏]-preserving-[+]ᵣ {x}) {y} = symmetry(_≡_) ([+][𝐏]-stepᵣ {x}{y})

instance
  step-preserving-[+]ᵣ : ∀{s}{x} → Preserving₁(step s) (x +_)(x +_)
  step-preserving-[+]ᵣ {Sign.➕}{x} = [𝐒]-preserving-[+]ᵣ {x}
  step-preserving-[+]ᵣ {Sign.➖}{x} = [𝐏]-preserving-[+]ᵣ {x}

instance
  step-preserving-[+]ₗ : ∀{s}{x} → Preserving₁(step s) (_+ x)(_+ x)
  step-preserving-[+]ₗ {Sign.➕}{x} = [𝐒]-preserving-[+]ₗ {x}
  step-preserving-[+]ₗ {Sign.➖}{x} = [𝐏]-preserving-[+]ₗ {x}

[−]-preserves-[⋅]ₗ : ∀{x y} → ((− x) ⋅ y ≡ −(x ⋅ y))
[−]-preserves-[⋅]ₗ {𝟎}     {𝟎}     = [≡]-intro
[−]-preserves-[⋅]ₗ {𝟎}     {+𝐒ₙ y} = [≡]-intro
[−]-preserves-[⋅]ₗ {+𝐒ₙ x} {𝟎}     = [≡]-intro
[−]-preserves-[⋅]ₗ {+𝐒ₙ x} {+𝐒ₙ y} = [≡]-intro
[−]-preserves-[⋅]ₗ {𝟎}     {−𝐒ₙ y} = [≡]-intro
[−]-preserves-[⋅]ₗ {+𝐒ₙ x} {−𝐒ₙ y} = [≡]-intro
[−]-preserves-[⋅]ₗ {−𝐒ₙ x} {𝟎}     = [≡]-intro
[−]-preserves-[⋅]ₗ {−𝐒ₙ x} {+𝐒ₙ y} = [≡]-intro
[−]-preserves-[⋅]ₗ {−𝐒ₙ x} {−𝐒ₙ y} = [≡]-intro

[−]-preserves-[⋅]ᵣ : ∀{x y} → (x ⋅ (− y) ≡ −(x ⋅ y))
[−]-preserves-[⋅]ᵣ {𝟎}     {𝟎}     = [≡]-intro
[−]-preserves-[⋅]ᵣ {𝟎}     {+𝐒ₙ y} = [≡]-intro
[−]-preserves-[⋅]ᵣ {+𝐒ₙ x} {𝟎}     = [≡]-intro
[−]-preserves-[⋅]ᵣ {+𝐒ₙ x} {+𝐒ₙ y} = [≡]-intro
[−]-preserves-[⋅]ᵣ {𝟎}     {−𝐒ₙ y} = [≡]-intro
[−]-preserves-[⋅]ᵣ {+𝐒ₙ x} {−𝐒ₙ y} = [≡]-intro
[−]-preserves-[⋅]ᵣ {−𝐒ₙ x} {𝟎}     = [≡]-intro
[−]-preserves-[⋅]ᵣ {−𝐒ₙ x} {+𝐒ₙ y} = [≡]-intro
[−]-preserves-[⋅]ᵣ {−𝐒ₙ x} {−𝐒ₙ y} = [≡]-intro

[−]-antipreserves-[⋅] : ∀{x y} → ((− x) ⋅ (− y) ≡ x ⋅ y)
[−]-antipreserves-[⋅] {𝟎}     {𝟎}     = [≡]-intro
[−]-antipreserves-[⋅] {𝟎}     {+𝐒ₙ y} = [≡]-intro
[−]-antipreserves-[⋅] {+𝐒ₙ x} {𝟎}     = [≡]-intro
[−]-antipreserves-[⋅] {+𝐒ₙ x} {+𝐒ₙ y} = [≡]-intro
[−]-antipreserves-[⋅] {𝟎}     {−𝐒ₙ y} = [≡]-intro
[−]-antipreserves-[⋅] {+𝐒ₙ x} {−𝐒ₙ y} = [≡]-intro
[−]-antipreserves-[⋅] {−𝐒ₙ x} {𝟎}     = [≡]-intro
[−]-antipreserves-[⋅] {−𝐒ₙ x} {+𝐒ₙ y} = [≡]-intro
[−]-antipreserves-[⋅] {−𝐒ₙ x} {−𝐒ₙ y} = [≡]-intro

signOn-preserves-[⋅]ₗ : ∀{x y}{s} → ((signOn s x) ⋅ y ≡ signOn s (x ⋅ y))
signOn-preserves-[⋅]ₗ {s = Sign.➕} = [≡]-intro
signOn-preserves-[⋅]ₗ {s = Sign.➖} = [−]-preserves-[⋅]ₗ

signOn-preserves-[⋅]ᵣ : ∀{x y}{s} → (x ⋅ (signOn s y) ≡ signOn s (x ⋅ y))
signOn-preserves-[⋅]ᵣ {s = Sign.➕} = [≡]-intro
signOn-preserves-[⋅]ᵣ {s = Sign.➖} = [−]-preserves-[⋅]ᵣ

signOn-antipreserves-[⋅] : ∀{x y}{s} → ((signOn s x) ⋅ (signOn s y) ≡ x ⋅ y)
signOn-antipreserves-[⋅] {s = Sign.➕} = [≡]-intro
signOn-antipreserves-[⋅] {s = Sign.➖} = [−]-antipreserves-[⋅]



[−]-of-[+𝐒ₙ] : ∀{x y} → (+𝐒ₙ x) − (+𝐒ₙ y) ≡ (+ₙ x) − (+ₙ y)
[−]-of-[+𝐒ₙ] {y = ℕ.𝟎}   = [≡]-intro
[−]-of-[+𝐒ₙ] {y = ℕ.𝐒 _} = [≡]-intro

[−]-of-[−𝐒ₙ] : ∀{x y} → (−𝐒ₙ x) − (−𝐒ₙ y) ≡ (−ₙ x) − (−ₙ y)
[−]-of-[−𝐒ₙ] {ℕ.𝟎}   {ℕ.𝟎}   = [≡]-intro
[−]-of-[−𝐒ₙ] {ℕ.𝟎}   {ℕ.𝐒 y} = [≡]-intro
[−]-of-[−𝐒ₙ] {ℕ.𝐒 x} {ℕ.𝟎}   = [≡]-intro
[−]-of-[−𝐒ₙ] {ℕ.𝐒 x} {ℕ.𝐒 y} = [≡]-intro

[−]-of-[𝐒] : ∀{x y} → (𝐒(x) − 𝐒(y) ≡ x − y)
[−]-of-[𝐒] {+ₙ x} {+ₙ y} = [−]-of-[+𝐒ₙ] {x}{y}
[−]-of-[𝐒] {+ₙ x} {−𝐒ₙ ℕ.𝟎} = [≡]-intro
[−]-of-[𝐒] {+ₙ x} {−𝐒ₙ ℕ.𝐒 y} = [≡]-intro
[−]-of-[𝐒] {−𝐒ₙ ℕ.𝟎} {+ₙ ℕ.𝟎} = [≡]-intro
[−]-of-[𝐒] {−𝐒ₙ ℕ.𝟎} {+ₙ ℕ.𝐒 y} = [≡]-intro
[−]-of-[𝐒] {−𝐒ₙ ℕ.𝐒 x} {+ₙ ℕ.𝟎} = [≡]-intro
[−]-of-[𝐒] {−𝐒ₙ ℕ.𝐒 x} {+ₙ ℕ.𝐒 y} = [≡]-intro
[−]-of-[𝐒] {−𝐒ₙ ℕ.𝟎} {−𝐒ₙ ℕ.𝟎} = [≡]-intro
[−]-of-[𝐒] {−𝐒ₙ ℕ.𝟎} {−𝐒ₙ ℕ.𝐒 y} = [≡]-intro
[−]-of-[𝐒] {−𝐒ₙ ℕ.𝐒 x} {−𝐒ₙ ℕ.𝟎} = [≡]-intro
[−]-of-[𝐒] {−𝐒ₙ ℕ.𝐒 x} {−𝐒ₙ ℕ.𝐒 y} = [≡]-intro

[−]-of-[𝐏] : ∀{x y} → (𝐏(x) − 𝐏(y) ≡ x − y)
[−]-of-[𝐏] {+ₙ ℕ.𝟎} {+ₙ ℕ.𝟎} = [≡]-intro
[−]-of-[𝐏] {+ₙ ℕ.𝟎} {+ₙ ℕ.𝐒 ℕ.𝟎} = [≡]-intro
[−]-of-[𝐏] {+ₙ ℕ.𝟎} {+ₙ ℕ.𝐒 (ℕ.𝐒 y)} = [≡]-intro
[−]-of-[𝐏] {+ₙ ℕ.𝐒 x} {+ₙ ℕ.𝟎} = [≡]-intro
[−]-of-[𝐏] {+ₙ ℕ.𝐒 x} {+ₙ ℕ.𝐒 y} = symmetry(_≡_) ([−]-of-[+𝐒ₙ] {x}{y})
[−]-of-[𝐏] {+ₙ ℕ.𝟎} {−𝐒ₙ y} = [≡]-intro
[−]-of-[𝐏] {+ₙ ℕ.𝐒 x} {−𝐒ₙ y} = [≡]-intro
[−]-of-[𝐏] {−𝐒ₙ x} {+ₙ ℕ.𝟎} = [≡]-intro
[−]-of-[𝐏] {−𝐒ₙ x} {+ₙ ℕ.𝐒 ℕ.𝟎} = [≡]-intro
[−]-of-[𝐏] {−𝐒ₙ x} {+ₙ ℕ.𝐒 (ℕ.𝐒 y)} = [≡]-intro
[−]-of-[𝐏] {−𝐒ₙ x} {−𝐒ₙ y} = [−]-of-[−𝐒ₙ] {ℕ.𝐒 x}{ℕ.𝐒 y}

[+ₙ][−₀][−]-preserving : ∀{x y} → (x ℕ.≥ y) → ((+ₙ(x ℕ.−₀ y)) ≡ ((+ₙ x) − (+ₙ y)))
[+ₙ][−₀][−]-preserving ℕ.min = [≡]-intro
[+ₙ][−₀][−]-preserving {ℕ.𝐒 x}{ℕ.𝐒 y} (ℕ.succ p) = [+ₙ][−₀][−]-preserving {x}{y} p 🝖 symmetry(_≡_) ([−]-of-[+𝐒ₙ] {x}{y})



instance
  [+]-associativity : Associativity(_+_)
  Associativity.proof [+]-associativity {x}{y}{z} = ℤ-sign-recursion(Names.AssociativeOn(_+_) x y) neg zero pos z where
    zero =
      (x + y) + 𝟎 🝖[ _≡_ ]-[ identityᵣ(_+_)(𝟎) ]
      x + y       🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x) (identityᵣ(_+_)(𝟎)) ]-sym
      x + (y + 𝟎) 🝖-end
    pos = \z prev →
      (x + y) + (+𝐒ₙ(z))   🝖[ _≡_ ]-[]
      (x + y) + 𝐒(+ₙ(z))   🝖[ _≡_ ]-[ [+][𝐒]-stepᵣ {x + y}{+ₙ(z)} ]
      𝐒((x + y) + (+ₙ(z))) 🝖[ _≡_ ]-[ congruence₁(𝐒) prev ]
      𝐒(x + (y + (+ₙ(z)))) 🝖[ _≡_ ]-[ [+][𝐒]-stepᵣ {x}{y + (+ₙ z)} ]-sym
      x + 𝐒(y + (+ₙ(z)))   🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x) ([+][𝐒]-stepᵣ {y}{+ₙ z}) ]-sym
      x + (y + 𝐒(+ₙ(z)))   🝖[ _≡_ ]-[]
      x + (y + (+𝐒ₙ(z)))   🝖-end
    neg = \z prev →
      (x + y) + (−𝐒ₙ(z))   🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x + y) [𝐏]-negative ]-sym
      (x + y) + 𝐏(−ₙ(z))   🝖[ _≡_ ]-[ [+][𝐏]-stepᵣ {x + y}{−ₙ(z)} ]
      𝐏((x + y) + (−ₙ(z))) 🝖[ _≡_ ]-[ congruence₁(𝐏) prev ]
      𝐏(x + (y + (−ₙ(z)))) 🝖[ _≡_ ]-[ [+][𝐏]-stepᵣ {x}{y + (−ₙ z)} ]-sym
      x + 𝐏(y + (−ₙ(z)))   🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x) ([+][𝐏]-stepᵣ {y}{−ₙ z}) ]-sym
      x + (y + 𝐏(−ₙ(z)))   🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x) (congruence₂ᵣ(_+_)(y) [𝐏]-negative) ]
      x + (y + (−𝐒ₙ(z)))   🝖-end

instance
  [+]-semi : Semi(_+_)
  [+]-semi = intro

instance
  [+]-monoid : Monoid(_+_)
  [+]-monoid = intro

open import Logic.Propositional.Theorems
open import Numeral.Natural.Oper.Proofs.Structure using (ℕ-nonZero)
instance
  ℤ-nonZero : NonIdentityRelation([+]-monoid)
  NonIdentityRelation.NonIdentity ℤ-nonZero = NonZero
  NonIdentityRelation.proof       ℤ-nonZero = [↔]-transitivity (NonIdentityRelation.proof ℕ-nonZero) ([↔]-intro (_∘ absₙ-zero) (_∘ congruence₁(absₙ)))

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

signed-inverse : ∀{x} → (signed0 (sign0 x) (absₙ x) ≡ x)
signed-inverse {+𝐒ₙ _} = [≡]-intro
signed-inverse {𝟎}     = [≡]-intro
signed-inverse {−𝐒ₙ _} = [≡]-intro

sign0-inverse : ∀{x}{y} → (sign0(signed0 x (ℕ.𝐒(y))) ≡ x)
sign0-inverse {Sign.➕} {y} = [≡]-intro
sign0-inverse {Sign.𝟎}  {y} = [≡]-intro
sign0-inverse {Sign.➖} {y} = [≡]-intro

absₙ-inverse : ∀{x}{y} → (x ≢ Sign.𝟎) → (absₙ(signed0 x y) ≡ y)
absₙ-inverse {Sign.➕} {ℕ.𝟎}   _ = [≡]-intro
absₙ-inverse {Sign.➕} {ℕ.𝐒 y} _ = [≡]-intro
absₙ-inverse {Sign.➖} {ℕ.𝟎}   _ = [≡]-intro
absₙ-inverse {Sign.➖} {ℕ.𝐒 y} _ = [≡]-intro
absₙ-inverse {Sign.𝟎} {ℕ.𝟎}    _ = [≡]-intro
absₙ-inverse {Sign.𝟎} {ℕ.𝐒 y}  p with () ← p [≡]-intro

absₙ-of-[−] : ∀{x} → (absₙ(− x) ≡ absₙ x)
absₙ-of-[−] {+𝐒ₙ _} = [≡]-intro
absₙ-of-[−] {𝟎}     = [≡]-intro
absₙ-of-[−] {−𝐒ₙ _} = [≡]-intro

[⋅]-equality : ∀{x y z} → (x ⋅ y ≡ z) ↔ (sign0(x) Sign.⨯ sign0(y) ≡ sign0 z) ∧ (absₙ(x) ℕ.⋅ absₙ(y) ≡ absₙ(z))
[⋅]-equality {x}{y}{z} = [↔]-intro (Tuple.uncurry l) r where
  l : ∀{x y z} → (sign0(x) Sign.⨯ sign0(y) ≡ sign0 z) → (absₙ(x) ℕ.⋅ absₙ(y) ≡ absₙ(z)) → (x ⋅ y ≡ z)
  l{x}{y}{z} p q = congruence₂(signed0) p q 🝖 signed-inverse

  r : ∀{x y z} → (x ⋅ y ≡ z) → (sign0(x) Sign.⨯ sign0(y) ≡ sign0 z) ∧ (absₙ(x) ℕ.⋅ absₙ(y) ≡ absₙ(z))
  r{x}{y}{z} p = [∧]-intro (symmetry(_≡_) (preserving₂(sign0)(_⋅_)(Sign._⨯_)) 🝖 congruence₁(sign0) p) (symmetry(_≡_) (preserving₂(absₙ)(_⋅_)(ℕ._⋅_) {x}{y}) 🝖 congruence₁(absₙ) p)

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
  [⋅]-identity : Identity(_⋅_)(𝟏)
  [⋅]-identity = intro

instance
  [⋅]-commutativity : Commutativity(_⋅_)
  Commutativity.proof [⋅]-commutativity {x}{y} = congruence₂(signed0) (commutativity(Sign._⨯_)) (commutativity(ℕ._⋅_) {absₙ x}{absₙ y})

instance
  [⋅]-absorberₗ : Absorberₗ(_⋅_)(𝟎)
  Absorberₗ.proof [⋅]-absorberₗ {+𝐒ₙ x} = [≡]-intro
  Absorberₗ.proof [⋅]-absorberₗ {𝟎}     = [≡]-intro
  Absorberₗ.proof [⋅]-absorberₗ {−𝐒ₙ x} = [≡]-intro

instance
  [⋅]-absorberᵣ : Absorberᵣ(_⋅_)(𝟎)
  Absorberᵣ.proof [⋅]-absorberᵣ {+𝐒ₙ x} = [≡]-intro
  Absorberᵣ.proof [⋅]-absorberᵣ {𝟎}     = [≡]-intro
  Absorberᵣ.proof [⋅]-absorberᵣ {−𝐒ₙ x} = [≡]-intro

[⋅]-negative-identityₗ : ∀{x} → (−𝟏 ⋅ x ≡ − x)
[⋅]-negative-identityₗ {+𝐒ₙ x} = [≡]-intro
[⋅]-negative-identityₗ {𝟎}     = [≡]-intro
[⋅]-negative-identityₗ {−𝐒ₙ x} = [≡]-intro

[⋅]-negative-identityᵣ : ∀{x} → (x ⋅ −𝟏 ≡ − x)
[⋅]-negative-identityᵣ {+𝐒ₙ x} = [≡]-intro
[⋅]-negative-identityᵣ {𝟎}     = [≡]-intro
[⋅]-negative-identityᵣ {−𝐒ₙ x} = [≡]-intro

[⋅][𝐏]-stepᵣ : ∀{x y} → (x ⋅ 𝐏(y) ≡ (− x) + (x ⋅ y))
[⋅][𝐒]-stepᵣ : ∀{x y} → (x ⋅ 𝐒(y) ≡ x + (x ⋅ y))

[⋅][𝐏]-stepᵣ {x} {+ₙ ℕ.𝟎} =
  x ⋅ −𝟏          🝖[ _≡_ ]-[ [⋅]-negative-identityᵣ ]
  − x             🝖[ _≡_ ]-[ identityᵣ(_+_)(𝟎) ]-sym
  (− x) + 𝟎       🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(− x) (absorberᵣ(_⋅_)(𝟎)) ]-sym
  (− x) + (x ⋅ 𝟎) 🝖-end
[⋅][𝐏]-stepᵣ {x} {+ₙ ℕ.𝐒 y} =
  x ⋅ (+ₙ y)                 🝖[ _≡_ ]-[ identityₗ(_+_)(𝟎) ]-sym
  𝟎 + (x ⋅ (+ₙ y))           🝖[ _≡_ ]-[ congruence₂ₗ(_+_)(x ⋅ (+ₙ y)) (inverseFunctionₗ(_+_)(−_) {x}) ]-sym
  ((− x) + x) + (x ⋅ (+ₙ y)) 🝖[ _≡_ ]-[ associativity(_+_) {− x}{x}{x ⋅ (+ₙ y)} ]
  (− x) + (x + (x ⋅ (+ₙ y))) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(− x) ([⋅][𝐒]-stepᵣ {x}{+ₙ y}) ]-sym
  (− x) + (x ⋅ (+𝐒ₙ y))      🝖-end
[⋅][𝐏]-stepᵣ {+ₙ x} {−𝐒ₙ y} =
  (+ₙ x) ⋅ (−𝐒ₙ ℕ.𝐒 y)              🝖[ _≡_ ]-[ [−]-preserves-[⋅]ᵣ {+ₙ x}{+𝐒ₙ ℕ.𝐒 y} ]
  −((+ₙ x) ⋅ (+𝐒ₙ ℕ.𝐒 y))           🝖[ _≡_ ]-[ congruence₁(−_) ([⋅][𝐒]-stepᵣ {+ₙ x} {+𝐒ₙ y}) ]
  −((+ₙ x) + ((+ₙ x) ⋅ (+𝐒ₙ y)))    🝖[ _≡_ ]-[ preserving₂(−_) (_+_)(_+_) {+ₙ x}{(+ₙ x) ⋅ (+𝐒ₙ y)} ]
  (−(+ₙ x)) + (−((+ₙ x) ⋅ (+𝐒ₙ y))) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(−(+ₙ x)) ([−]-preserves-[⋅]ᵣ {+ₙ x}{+𝐒ₙ y}) ]-sym
  (−(+ₙ x)) + ((+ₙ x) ⋅ (−𝐒ₙ y))    🝖-end
[⋅][𝐏]-stepᵣ {−𝐒ₙ x} {−𝐒ₙ y} =
  (−𝐒ₙ x) ⋅ 𝐏 (−𝐒ₙ y)               🝖[ _≡_ ]-[]
  (−𝐒ₙ x) ⋅ (−𝐒ₙ ℕ.𝐒 y)             🝖[ _≡_ ]-[ [−]-antipreserves-[⋅] {+𝐒ₙ x}{+𝐒ₙ(ℕ.𝐒 y)} ]
  (+𝐒ₙ x) ⋅ (+𝐒ₙ ℕ.𝐒 y)             🝖[ _≡_ ]-[ [⋅][𝐒]-stepᵣ {+𝐒ₙ x}{+𝐒ₙ y} ]
  (+𝐒ₙ x) + ((+𝐒ₙ x) ⋅ (+𝐒ₙ y))     🝖[ _≡_ ]-[]
  (− (−𝐒ₙ x)) + ((−𝐒ₙ x) ⋅ (−𝐒ₙ y)) 🝖-end

[⋅][𝐒]-stepᵣ {x} {−𝐒ₙ ℕ.𝟎} =
  x ⋅ 𝟎        🝖[ _≡_ ]-[ absorberᵣ(_⋅_)(𝟎) ]
  𝟎            🝖[ _≡_ ]-[ inverseFunctionᵣ(_+_)(−_) {x} ]-sym
  x + (− x)    🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x) [⋅]-negative-identityᵣ ]-sym
  x + (x ⋅ −𝟏) 🝖-end
[⋅][𝐒]-stepᵣ {x} {−𝐒ₙ(ℕ.𝐒 y)} =
  x ⋅ (−𝐒ₙ y)                 🝖[ _≡_ ]-[ identityₗ(_+_)(𝟎) ]-sym
  𝟎 + (x ⋅ (−𝐒ₙ y))           🝖[ _≡_ ]-[ congruence₂ₗ(_+_)((x) ⋅ (−𝐒ₙ y)) (inverseFunctionᵣ(_+_)(−_) {x}) ]-sym
  (x + (− x)) + (x ⋅ (−𝐒ₙ y)) 🝖[ _≡_ ]-[ associativity(_+_) {x}{−(x)}{(x) ⋅ (−𝐒ₙ y)} ]
  x + ((− x) + (x ⋅ (−𝐒ₙ y))) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x) ([⋅][𝐏]-stepᵣ {x}{−𝐒ₙ y}) ]-sym
  x + (x ⋅ 𝐏(−𝐒ₙ y))          🝖[ _≡_ ]-[]
  x + (x ⋅ (−𝐒ₙ ℕ.𝐒 y))       🝖-end
[⋅][𝐒]-stepᵣ {+ₙ x} {+ₙ y} =
  (+ₙ x) ⋅ 𝐒(+ₙ y)           🝖[ _≡_ ]-[]
  (+ₙ x) ⋅ (+ₙ(ℕ.𝐒(y)))      🝖[ _≡_ ]-[ preserving₂(+ₙ_) (ℕ._⋅_)(_⋅_) {x}{ℕ.𝐒(y)} ]-sym
  (+ₙ (x ℕ.⋅ ℕ.𝐒(y)))        🝖[ _≡_ ]-[]
  (+ₙ (x ℕ.+ (x ℕ.⋅ y)))     🝖[ _≡_ ]-[]
  (+ₙ x) + (+ₙ(x ℕ.⋅ y))     🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(+ₙ x) (preserving₂(+ₙ_) (ℕ._⋅_) (_⋅_) {x}{y}) ]
  (+ₙ x) + ((+ₙ x) ⋅ (+ₙ y)) 🝖-end
[⋅][𝐒]-stepᵣ {−𝐒ₙ x} {+ₙ y} =
  (−𝐒ₙ x) ⋅ (+𝐒ₙ y)               🝖[ _≡_ ]-[]
  (−(+𝐒ₙ x)) ⋅ (+𝐒ₙ y)            🝖[ _≡_ ]-[ [−]-preserves-[⋅]ₗ {+𝐒ₙ x}{+𝐒ₙ y} ]
  −((+𝐒ₙ x) ⋅ (+𝐒ₙ y))            🝖[ _≡_ ]-[ congruence₁(−_) ([⋅][𝐒]-stepᵣ {+𝐒ₙ x} {+ₙ y}) ]
  −((+𝐒ₙ x) + ((+𝐒ₙ x) ⋅ (+ₙ y))) 🝖[ _≡_ ]-[ preserving₂(−_) (_+_)(_+_) {+𝐒ₙ x}{(+𝐒ₙ x) ⋅ (+ₙ y)} ]
  (−𝐒ₙ x) − ((+𝐒ₙ x) ⋅ (+ₙ y))    🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(−𝐒ₙ x) ([−]-preserves-[⋅]ₗ {+𝐒ₙ x}{+ₙ y}) ]-sym
  (−𝐒ₙ x) + ((−𝐒ₙ x) ⋅ (+ₙ y))    🝖-end

[⋅]-step-stepᵣ : ∀{x y}{s} → (x ⋅ step s y ≡ (signOn s x) + (x ⋅ y))
[⋅]-step-stepᵣ {x} {y} {Sign.➕} = [⋅][𝐒]-stepᵣ
[⋅]-step-stepᵣ {x} {y} {Sign.➖} = [⋅][𝐏]-stepᵣ

open import Structure.Operator.Proofs.Util
instance
  [⋅][+]-distributivityₗ : Distributivityₗ(_⋅_)(_+_)
  Distributivityₗ.proof [⋅][+]-distributivityₗ {x} {y} {z} = ℤ-signed-step-recursion(Names.DistributiveOnₗ(_⋅_)(_+_) x y) zero next z where
    zero =
      x ⋅ (y + 𝟎)       🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_)(x) (identityᵣ(_+_)(𝟎)) ]
      x ⋅ y             🝖[ _≡_ ]-[ identityᵣ(_+_)(𝟎) ]-sym
      (x ⋅ y) + 𝟎       🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x ⋅ y) (absorberᵣ(_⋅_)(𝟎)) ]-sym
      (x ⋅ y) + (x ⋅ 𝟎) 🝖-end
    next = \s z prev →
      x ⋅ (y + step s (signed s z))               🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_)(x) (preserving₁(step s) (y +_)(y +_) ⦃ step-preserving-[+]ᵣ {s}{y} ⦄ {signed s z}) ]-sym
      x ⋅ step s (y + (signed s z))               🝖[ _≡_ ]-[ [⋅]-step-stepᵣ {x}{y + signed s z}{s} ]
      (signOn s x) + (x ⋅ (y + (signed s z)))     🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(signOn s x) prev ]
      (signOn s x) + ((x ⋅ y) + (x ⋅ signed s z)) 🝖[ _≡_ ]-[ One.commuteₗ-assocᵣ {a = signOn s x}{b = x ⋅ y}{c = x ⋅ signed s z} ]
      (x ⋅ y) + ((signOn s x) + (x ⋅ signed s z)) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x ⋅ y) ([⋅]-step-stepᵣ {x}{signed s z}{s}) ]-sym
      (x ⋅ y) + (x ⋅ step s (signed s z))         🝖-end
  {-
    x ⋅ (y + z)                                                                                                                     🝖[ _≡_ ]-[]
    signed0 ((sign0 x) Sign.⨯ (sign0(y + z))) ((absₙ x) ℕ.⋅ (absₙ(y + z)))                                                          🝖[ _≡_ ]-[ {!congruence₂(signed0) ? ?!} ]
    signed0 ((sign0 x) Sign.⨯ sign0(y + z)) ((absₙ x) ℕ.⋅ (absₙ(y + z)))                                                          🝖[ _≡_ ]-[ {!!} ]
    (signed0 ((sign0 x) Sign.⨯ (sign0 y)) ((absₙ x) ℕ.⋅ (absₙ y))) + (signed0 ((sign0 x) Sign.⨯ (sign0 z)) ((absₙ x) ℕ.⋅ (absₙ z))) 🝖[ _≡_ ]-[]
    (x ⋅ y) + (x ⋅ z)                                                                                                               🝖-end
    where
      sign0-proof : ∀{x y z} → ((sign0 x) Sign.⨯ sign0(y + z) ≡ (sign0(x) + sign0(z)) Sign.⨯ (sign0(x) + sign0(z)))
  -}

instance
  [⋅]-associativity : Associativity(_⋅_)
  Associativity.proof [⋅]-associativity {x}{y}{z} = ℤ-signed-step-recursion(Names.AssociativeOn(_⋅_) x y) zero next z where
    zero =
      (x ⋅ y) ⋅ 𝟎 🝖[ _≡_ ]-[ absorberᵣ(_⋅_)(𝟎) ]
      𝟎           🝖[ _≡_ ]-[ absorberᵣ(_⋅_)(𝟎) ]-sym
      x ⋅ 𝟎       🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_)(x) (absorberᵣ(_⋅_)(𝟎)) ]-sym
      x ⋅ (y ⋅ 𝟎) 🝖-end
    next = \s z prev →
      (x ⋅ y) ⋅ step s (signed s z)                 🝖[ _≡_ ]-[ [⋅]-step-stepᵣ {x ⋅ y}{signed s z}{s} ]
      (signOn s (x ⋅ y)) + ((x ⋅ y) ⋅ (signed s z)) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(signOn s (x ⋅ y)) prev ]
      (signOn s (x ⋅ y)) + (x ⋅ (y ⋅ (signed s z))) 🝖[ _≡_ ]-[ congruence₂ₗ(_+_)(x ⋅ (y ⋅ (signed s z))) (signOn-preserves-[⋅]ᵣ {x}{y}{s}) ]-sym
      (x ⋅ signOn s y) + (x ⋅ (y ⋅ (signed s z)))   🝖[ _≡_ ]-[ distributivityₗ(_⋅_)(_+_) {x}{signOn s y}{y ⋅ (signed s z)} ]-sym
      x ⋅ (signOn s y + (y ⋅ (signed s z)))         🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_)(x) ([⋅]-step-stepᵣ {y}{signed s z}{s}) ]-sym
      x ⋅ (y ⋅ step s (signed s z)) 🝖-end
    {-
    congruence₂(signed0)
      (
        (sign0(signed0 (sign0 x Sign.⨯ sign0 y) (absₙ x ℕ.⋅ absₙ y)) Sign.⨯ sign0(z)) 🝖[ _≡_ ]-[ {!!} ]
        (sign0(x) Sign.⨯ (sign0(y) Sign.⨯ sign0(z))) 🝖[ _≡_ ]-[ congruence₂ᵣ(Sign._⨯_)(sign0(x)) sign-of-[⋅] ]-sym
        (sign0(x) Sign.⨯ sign0(y ⋅ z)) 🝖-end
      )
      -- associativity(Sign0._⨯_)
      -- (congruence₂ₗ(Sign._⨯_)(sign0 z) sign0-inverse                                                  🝖 associativity(Sign._⨯_)                      🝖 symmetry(_≡_) (congruence₂ᵣ(Sign._⨯_)(sign0(x)) (sign-of-[⋅] {y}{z})))
      {!!}
      -- (congruence₂ₗ(ℕ._⋅_)   (absₙ(z)) (absₙ-inverse{sign0(x) Sign.⨯ sign0(y)}{absₙ(x) ℕ.⋅ absₙ(y)})  🝖 associativity(ℕ._⋅_){absₙ x}{absₙ y}{absₙ z} 🝖 symmetry(_≡_) (congruence₂ᵣ(ℕ._⋅_)   (absₙ (x)) (absₙ-of-[⋅] {y}{z})))
    -}

instance
  [⋅]-semi : Semi(_⋅_)
  [⋅]-semi = intro

instance
  [⋅]-monoid : Monoid(_⋅_)
  [⋅]-monoid = intro

open import Structure.Operator.Proofs
instance
  [⋅][+]-distributivityᵣ : Distributivityᵣ(_⋅_)(_+_)
  [⋅][+]-distributivityᵣ = [↔]-to-[→] OneTypeTwoOp.distributivity-equivalence-by-commutativity [⋅][+]-distributivityₗ

instance
  [⋅][−]-distributivityₗ : Distributivityₗ(_⋅_)(_−_)
  Distributivityₗ.proof [⋅][−]-distributivityₗ {x} {y} {z} =
    x ⋅ (y − z)           🝖[ _≡_ ]-[]
    x ⋅ (y + (− z))       🝖[ _≡_ ]-[ distributivityₗ(_⋅_)(_+_) ]
    (x ⋅ y) + (x ⋅ (− z)) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x ⋅ y) [−]-preserves-[⋅]ᵣ ]
    (x ⋅ y) + (−(x ⋅ z))  🝖[ _≡_ ]-[]
    (x ⋅ y) − (x ⋅ z)     🝖-end

instance
  [⋅][−]-distributivityᵣ : Distributivityᵣ(_⋅_)(_−_)
  [⋅][−]-distributivityᵣ = [↔]-to-[→] OneTypeTwoOp.distributivity-equivalence-by-commutativity [⋅][−]-distributivityₗ

instance
  [⋅][+]-distributivity : Distributivity(_⋅_)(_+_)
  [⋅][+]-distributivity = intro

instance
  [+][⋅]-ring : Ring(_+_)(_⋅_)
  [+][⋅]-ring = record{}

{-
[𝄩]-by-abs-[−] : ∀{x y} → (x 𝄩 y ≡ absₙ(x − y))
[𝄩]-by-abs-[−] {+ₙ ℕ.𝟎} {+ₙ ℕ.𝟎} = [≡]-intro
[𝄩]-by-abs-[−] {+ₙ ℕ.𝟎} {+ₙ ℕ.𝐒 y} = [≡]-intro
[𝄩]-by-abs-[−] {+ₙ ℕ.𝐒 x} {+ₙ ℕ.𝟎} = [≡]-intro
[𝄩]-by-abs-[−] {+ₙ ℕ.𝐒 x} {+ₙ ℕ.𝐒 y} = {!!}
[𝄩]-by-abs-[−] {+ₙ ℕ.𝟎} {−𝐒ₙ y} = [≡]-intro
[𝄩]-by-abs-[−] {+ₙ ℕ.𝐒 x} {−𝐒ₙ y} = {!!}
[𝄩]-by-abs-[−] {−𝐒ₙ x} {+ₙ ℕ.𝟎} = [≡]-intro
[𝄩]-by-abs-[−] {−𝐒ₙ x} {+ₙ ℕ.𝐒 y} = {!!}
[𝄩]-by-abs-[−] {−𝐒ₙ x} {−𝐒ₙ y} = {!!}
-}
