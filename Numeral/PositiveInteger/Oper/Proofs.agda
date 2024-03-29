module Numeral.PositiveInteger.Oper.Proofs where

open import Functional
open import Function.Equals
open import Function.Iteration
open import Function.Iteration.Proofs
open import Logic.Propositional
open import Logic.Predicate
import      Numeral.Natural as ℕ
import      Numeral.Natural.Oper as ℕ
open import Numeral.PositiveInteger
open import Numeral.PositiveInteger.Oper
open import Relator.Equals
open import Relator.Equals.Proofs
import      Function.Names as Names
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Multi
open import Structure.Operator
open import Structure.Operator.Monoid
import      Structure.Operator.Names as Names
open import Structure.Operator.Proofs.Util
open import Structure.Operator.Proofs
open import Structure.Operator.Properties
open import Syntax.Transitivity
open import Type

-- TODO: Move stuff related to ℕ₊-to-ℕ

instance
  ℕ-ℕ₊-preserves-𝐒 : Preserving₁(toℕ)(𝐒)(ℕ.𝐒)
  Preserving.proof ℕ-ℕ₊-preserves-𝐒 = p where
    p : Names.Preserving₁(toℕ)(𝐒)(ℕ.𝐒)
    p {𝟏}   = [≡]-intro
    p {𝐒 x} = congruence₁(ℕ.𝐒) p

instance
  ℕ-ℕ₊-preserves-[+] : Preserving₂(toℕ)(_+_)(ℕ._+_)
  Preserving.proof ℕ-ℕ₊-preserves-[+] {x}{y} = p{x}{y} where
    p : Names.Preserving₂(toℕ)(_+_)(ℕ._+_)
    p {x} {𝟏}   = [≡]-intro
    p {x} {𝐒 y} = congruence₁(ℕ.𝐒) (p{x}{y})

instance
  ℕ-ℕ₊-preserves-[⋅] : Preserving₂(toℕ)(_⋅_)(ℕ._⋅_)
  Preserving.proof ℕ-ℕ₊-preserves-[⋅] {x}{y} = p{x}{y} where
    p : Names.Preserving₂(toℕ)(_⋅_)(ℕ._⋅_)
    p {x} {𝟏}   = [≡]-intro
    p {x} {𝐒 y} =
      toℕ (x + (x ⋅ y))                 🝖[ _≡_ ]-[ preserving₂(toℕ)(_+_)(ℕ._+_) {x}{x ⋅ y} ]
      (toℕ x) ℕ.+ (toℕ (x ⋅ y))         🝖[ _≡_ ]-[ congruence₁((toℕ x) ℕ.+_) (p{x}{y}) ]
      (toℕ x) ℕ.+ ((toℕ x) ℕ.⋅ (toℕ y)) 🝖[ _≡_ ]-end

instance
  𝐒ₙ-preserves-𝐒 : Preserving₁(𝐒ₙ)(ℕ.𝐒)(𝐒)
  Preserving.proof 𝐒ₙ-preserves-𝐒 = [≡]-intro

instance
  𝐒ₙ-preserves-[+] : Preserving₂(𝐒ₙ)(ℕ.𝐒 ∘₂ ℕ._+_)(_+_)
  Preserving.proof 𝐒ₙ-preserves-[+] {x}{y} = p{x}{y} where
    p : Names.Preserving₂(𝐒ₙ)(ℕ.𝐒 ∘₂ ℕ._+_)(_+_)
    p {x}{ℕ.𝟎}   = [≡]-intro
    p {x}{ℕ.𝐒 y} = congruence₁(𝐒) (p {x}{y})

{-instance
  𝐒ₙ-preserves-[⋅] : Preserving₂(𝐒ₙ)(ℕ.𝐒 ∘₂ ℕ._⋅_ )(_⋅_)
  Preserving.proof 𝐒ₙ-preserves-[⋅] = p where
    p : Names.Preserving₂(𝐒ₙ)(ℕ.𝐒 ∘₂ ℕ._⋅_ )(_⋅_)
    p {x}{ℕ.𝟎}   = {!!}
    p {x}{ℕ.𝐒 y} = {!!} 
-}
{-      𝐒ₙ (ℕ.𝐒(x ℕ.+ (x ℕ.⋅ ℕ.𝐒(y))))         🝖[ _≡_ ]-[ preserving₂(𝐒ₙ)(ℕ.𝐒 ∘₂ ℕ._+_)(_+_) ]
      (𝐒ₙ x) + (𝐒ₙ (x ℕ.⋅ ℕ.𝐒(y)))     🝖[ _≡_ ]-[]
      (𝐒ₙ x) + (𝐒ₙ (x ℕ.+ (x ℕ.⋅ y)))  🝖[ _≡_ ]-[ congruence₁((𝐒ₙ x) +_) (p{x}{y}) ]
      (𝐒ₙ x) + ((𝐒ₙ x) ⋅ (𝐒ₙ y)) 🝖[ _≡_ ]-end
-}

{-
instance
  toℕ-injective : Injective(toℕ)
  Injective.proof toℕ-injective {𝟏}   {𝟏}   p = [≡]-intro
  Injective.proof toℕ-injective {𝟏}   {𝐒 y} p = {!congruence₁(\x → ℕ-to-ℕ₊ x ⦃ ? ⦄) p!}
  Injective.proof toℕ-injective {𝐒 x} {𝟏}   p = {!preserving₁(toℕ)(𝐒)(ℕ.𝐒) 🝖 p!}
  Injective.proof toℕ-injective {𝐒 x} {𝐒 y} p = {!!}
-}

{-
module _ where
  [+]-repeatᵣ-𝐒 : ∀{x y z : ℕ} → (x + y ≡ repeatᵣ y (const 𝐒) z x)
  [+]-repeatᵣ-𝐒 {x} {𝟎}       = [≡]-intro
  [+]-repeatᵣ-𝐒 {x} {𝐒 y} {z} = congruence₁(𝐒) ([+]-repeatᵣ-𝐒 {x} {y} {z})

  [+]-repeatₗ-𝐒 : ∀{x y z : ℕ} → (x + y ≡ repeatₗ y (const ∘ 𝐒) x z)
  [+]-repeatₗ-𝐒 {x} {𝟎}       = [≡]-intro
  [+]-repeatₗ-𝐒 {x} {𝐒 y} {z} = congruence₁(𝐒) ([+]-repeatₗ-𝐒 {x} {y} {z})

  [⋅]-repeatᵣ-[+] : ∀{x y} → (x ⋅ y ≡ repeatᵣ y (_+_) x 0)
  [⋅]-repeatᵣ-[+] {x} {𝟎}   = [≡]-intro
  [⋅]-repeatᵣ-[+] {x} {𝐒 y} = congruence₁(x +_) ([⋅]-repeatᵣ-[+] {x} {y})

  [^]-repeatᵣ-[⋅] : ∀{x y} → (x ^ y ≡ repeatᵣ y (_⋅_) x 1)
  [^]-repeatᵣ-[⋅] {x} {𝟎}   = [≡]-intro
  [^]-repeatᵣ-[⋅] {x} {𝐒 y} = congruence₁(x ⋅_) ([^]-repeatᵣ-[⋅] {x} {y})
-}

instance
  [𝐒]-injective : Injective(𝐒)
  Injective.proof [𝐒]-injective [≡]-intro = [≡]-intro

[1+]-𝐒 : ∀{x : ℕ₊} → (𝟏 + x ≡ 𝐒(x))
[1+]-𝐒 {𝟏}   = [≡]-intro
[1+]-𝐒 {𝐒 x} = congruence₁(𝐒) ([1+]-𝐒 {x})

[+]-step : ∀{x y : ℕ₊} → (𝐒(x) + y) ≡ (x + 𝐒(y))
[+]-step {x} {𝟏}   = [≡]-intro
[+]-step {x} {𝐒 y} = congruence₁(𝐒) ([+]-step {x} {y})

[+]-commutativity-raw : Names.Commutativity(_+_)
[+]-commutativity-raw {𝟏}   {𝟏}   = [≡]-intro
[+]-commutativity-raw {𝟏}   {𝐒 y} = congruence₁(𝐒) ([+]-commutativity-raw {𝟏} {y})
[+]-commutativity-raw {𝐒 x} {𝟏}   = congruence₁(𝐒) ([+]-commutativity-raw {x} {𝟏})
[+]-commutativity-raw {𝐒 x} {𝐒 y} = congruence₁(𝐒) (congruence₁(𝐒) ([+]-commutativity-raw {x} {y}))

instance
  [+]-commutativity : Commutativity(_+_)
  [+]-commutativity = intro(\{x}{y} → [+]-commutativity-raw {x}{y})

[+]-associativity-raw : Names.Associativity(_+_)
[+]-associativity-raw {x} {y} {𝟏} = [≡]-intro
[+]-associativity-raw {x} {y} {𝐒 z} = congruence₁(𝐒) ([+]-associativity-raw {x} {y} {z})

instance
  [+]-associativity : Associativity(_+_)
  [+]-associativity = intro(\{x}{y}{z} → [+]-associativity-raw {x}{y}{z})

[⋅]-identityₗ-raw : Names.Identityₗ(_⋅_)(𝟏)
[⋅]-identityₗ-raw {𝟏}   = [≡]-intro
[⋅]-identityₗ-raw {𝐒 x} = congruence₁(𝐒) ([⋅]-identityₗ-raw {x}) -- commutativity(_+_) 🝖 congruence₁(𝐒) ([⋅]-identityₗ-raw {x})

[⋅]-identityᵣ-raw : Names.Identityᵣ(_⋅_)(𝟏)
[⋅]-identityᵣ-raw = [≡]-intro

instance
  [⋅]-identityₗ : Identityₗ(_⋅_)(𝟏)
  [⋅]-identityₗ = intro [⋅]-identityₗ-raw

instance
  [⋅]-identityᵣ : Identityᵣ(_⋅_)(𝟏)
  [⋅]-identityᵣ = intro [⋅]-identityᵣ-raw

instance
  [⋅]-identity : Identity(_⋅_)(𝟏)
  [⋅]-identity = intro

[⋅]-commutativity-raw : Names.Commutativity(_⋅_) -- TODO: Extract the proof of (x + (𝐒 x + 𝐒 y) ≡ y + (𝐒 x + 𝐒 y)). Note that the properties here can probably also be proven using Function.Repeat.Proofs
[⋅]-commutativity-raw {x} {𝟏}   = [≡]-intro
[⋅]-commutativity-raw {𝟏} {𝐒 y} = [≡]-intro
[⋅]-commutativity-raw {𝐒 x} {𝐒 y} =
  𝐒 x ⋅ 𝐒 y           🝖[ _≡_ ]-[]
  𝐒 x + (𝐒 x ⋅ y)     🝖-[ congruence₁(𝐒) (congruence₂-₂(_+_)(x) ([⋅]-commutativity-raw {𝐒 x} {y})) ]
  𝐒 x + (y ⋅ 𝐒 x)     🝖[ _≡_ ]-[]
  𝐒 x + (y ⋅ 𝐒 x)     🝖[ _≡_ ]-[]
  𝐒 x + (y + (y ⋅ x)) 🝖-[ congruence₁(𝐒) (associativity(_+_) {x}{y}{y ⋅ x}) ]-sym
  (𝐒 x + y) + (y ⋅ x) 🝖[ _≡_ ]-[]
  𝐒(x + y) + (y ⋅ x)  🝖-[ congruence₁(𝐒) (congruence₂(_+_) ([+]-commutativity-raw {x}{y}) ([⋅]-commutativity-raw {y}{x})) ]
  𝐒(y + x) + (x ⋅ y)  🝖[ _≡_ ]-[]
  (𝐒 y + x) + (x ⋅ y) 🝖-[ congruence₁(𝐒) (associativity(_+_) {y}{x}{x ⋅ y}) ]
  𝐒 y + (x + (x ⋅ y)) 🝖[ _≡_ ]-[]
  𝐒 y + (x ⋅ 𝐒 y)     🝖-[ congruence₁(𝐒) (congruence₂-₂(_+_)(y) ([⋅]-commutativity-raw {𝐒 y} {x})) ]-sym
  𝐒 y + (𝐒 y ⋅ x)     🝖[ _≡_ ]-[]
  𝐒 y ⋅ 𝐒 x           🝖-end

instance
  [⋅]-commutativity : Commutativity(_⋅_)
  [⋅]-commutativity = intro(\{x}{y} → [⋅]-commutativity-raw {x}{y})

[⋅][+]-distributivityᵣ-raw : Names.Distributivityᵣ(_⋅_)(_+_)
[⋅][+]-distributivityᵣ-raw {x} {y} {𝟏}   = [≡]-intro
[⋅][+]-distributivityᵣ-raw {x} {y} {𝐒 z} =
  (x + y) + ((x + y) ⋅ z)       🝖[ _≡_ ]-[ congruence₁((x + y) +_) ([⋅][+]-distributivityᵣ-raw {x} {y} {z}) ]
  (x + y) + ((x ⋅ z) + (y ⋅ z)) 🝖[ _≡_ ]-[ One.associate-commute4 {a = x}{y}{x ⋅ z}{y ⋅ z} ([+]-commutativity-raw{x = y}) ]
  (x + (x ⋅ z)) + (y + (y ⋅ z)) 🝖[ _≡_ ]-[]
  (x ⋅ 𝐒(z)) + (y ⋅ 𝐒(z))       🝖[ _≡_ ]-end

instance
  [⋅][+]-distributivityᵣ : Distributivityᵣ(_⋅_)(_+_)
  [⋅][+]-distributivityᵣ = intro(\{x}{y}{z} → [⋅][+]-distributivityᵣ-raw {x}{y}{z})

instance
  [⋅][+]-distributivityₗ : Distributivityₗ(_⋅_)(_+_)
  [⋅][+]-distributivityₗ = [↔]-to-[←] OneTypeTwoOp.distributivity-equivalence-by-commutativity [⋅][+]-distributivityᵣ

[⋅]-associativity-raw : Names.Associativity(_⋅_)
[⋅]-associativity-raw {x} {y} {𝟏} = [≡]-intro
[⋅]-associativity-raw {x} {y} {𝐒 z} =
  (x ⋅ y) + (x ⋅ y ⋅ z)   🝖[ _≡_ ]-[ congruence₂-₂(_+_)(x ⋅ y) ([⋅]-associativity-raw {x}{y}{z}) ]
  (x ⋅ y) + (x ⋅ (y ⋅ z)) 🝖[ _≡_ ]-[ distributivityₗ(_⋅_)(_+_) {x = x}{y = y}{z = y ⋅ z} ]-sym
  x ⋅ (y + (y ⋅ z))       🝖-end

instance
  [⋅]-associativity : Associativity(_⋅_)
  [⋅]-associativity = intro(\{x}{y}{z} → [⋅]-associativity-raw {x}{y}{z})

instance
  ℕ₊-multiplicative-monoid : Monoid(_⋅_)
  Monoid.binaryOperator     ℕ₊-multiplicative-monoid = [≡]-binaryOperator
  Monoid.identity-existence ℕ₊-multiplicative-monoid = [∃]-intro(𝟏)

[⋅]-with-[𝐒]ₗ : ∀{x y} → (𝐒(x) ⋅ y ≡ (x ⋅ y) + y)
[⋅]-with-[𝐒]ₗ {x}{y} =
  𝐒(x) ⋅ y          🝖[ _≡_ ]-[ congruence₁(_⋅ y) ([1+]-𝐒 {x}) ]-sym
  (x + 𝟏) ⋅ y       🝖[ _≡_ ]-[ [⋅][+]-distributivityᵣ-raw{x}{𝟏}{y} ]
  (x ⋅ y) + (𝟏 ⋅ y) 🝖[ _≡_ ]-[ congruence₁((x ⋅ y) +_) ([⋅]-identityₗ-raw {y}) ]
  (x ⋅ y) + y       🝖[ _≡_ ]-end

[⋅]-with-[𝐒]ᵣ : ∀{x y} → (x ⋅ 𝐒(y) ≡ x + (x ⋅ y))
[⋅]-with-[𝐒]ᵣ = [≡]-intro
