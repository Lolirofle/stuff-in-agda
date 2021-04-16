module Data.Boolean.Proofs where

import      Lvl
open import Data
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Logic using (_⊼_ ; _⊽_ ; _⊕_)
open        Data.Boolean.Operators.Programming
open import Data.Either as Either using (_‖_ ; Left ; Right)
open import Functional
open import Logic.IntroInstances
open import Logic.Propositional as Logic using (_∨_ ; _∧_ ; ¬_ ; _↔_ ; [⊤]-intro ; [↔]-intro ; [⊥]-elim ; [↔]-to-[←] ; [↔]-to-[→])
open import Logic.Predicate
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Operator.Monoid
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}
private variable P : Bool → Type{ℓ}
private variable a b c t f : Bool
private variable x y : Bool
private variable pt pf : ∀{b} → P(b)

---------------------------------------------
-- Eliminator

module _ {pt pf : T} where
  elim-nested : (elim pt pf (elim t f b) ≡ elim{T = const T} (elim pt pf t) (elim pt pf f) b)
  elim-nested{t = t}{f = f}{b = b} = elim{T = b ↦ (elim pt pf (elim t f b) ≡ elim(elim pt pf t) (elim pt pf f) b)} [≡]-intro [≡]-intro b

module _ {x : T} where
  elim-redundant : (elim{T = const T} x x b ≡ x)
  elim-redundant{b = b} = elim{T = b ↦ elim x x b ≡ x} [≡]-intro [≡]-intro b

elim-inverse : (elim 𝑇 𝐹 b ≡ b)
elim-inverse{b = b} = elim{T = b ↦ elim 𝑇 𝐹 b ≡ b} [≡]-intro [≡]-intro b

elim-anti-inverse : (elim 𝐹 𝑇 b ≡ ! b)
elim-anti-inverse {𝑇} = [≡]-intro
elim-anti-inverse {𝐹} = [≡]-intro

---------------------------------------------
-- Negation

[!]-no-fixpoints : ∀{b} → (! b ≢ b)
[!]-no-fixpoints {𝑇} ()
[!]-no-fixpoints {𝐹} ()

[!!]-elim : ∀{a} → (!(! a) ≡ a)
[!!]-elim {𝑇} = [≡]-intro
[!!]-elim {𝐹} = [≡]-intro
{-# REWRITE [!!]-elim #-}

---------------------------------------------
-- Idempotence

[&&]-idempotence-raw : ∀{a} → (a && a ≡ a)
[&&]-idempotence-raw {𝑇} = [≡]-intro
[&&]-idempotence-raw {𝐹} = [≡]-intro
{-# REWRITE [&&]-idempotence-raw #-}
instance
  [&&]-idempotence : Idempotence(_&&_)
  Idempotence.proof([&&]-idempotence) = [&&]-idempotence-raw

[||]-idempotence-raw : ∀{a} → (a || a ≡ a)
[||]-idempotence-raw {𝑇} = [≡]-intro
[||]-idempotence-raw {𝐹} = [≡]-intro
{-# REWRITE [||]-idempotence-raw #-}
instance
  [||]-idempotence : Idempotence(_||_)
  Idempotence.proof([||]-idempotence) = [||]-idempotence-raw
---------------------------------------------
-- Left anti-identities

[==]-anti-identityₗ : ∀{a} → (𝐹 == a ≡ ! a)
[==]-anti-identityₗ {𝑇} = [≡]-intro
[==]-anti-identityₗ {𝐹} = [≡]-intro
{-# REWRITE [==]-anti-identityₗ #-}

[!=]-anti-identityₗ : ∀{a} → (𝑇 != a ≡ ! a)
[!=]-anti-identityₗ {𝑇} = [≡]-intro
[!=]-anti-identityₗ {𝐹} = [≡]-intro
{-# REWRITE [!=]-anti-identityₗ #-}

---------------------------------------------
-- Right anti-identities

[==]-anti-identityᵣ : ∀{a} → (a == 𝐹 ≡ ! a)
[==]-anti-identityᵣ {𝑇} = [≡]-intro
[==]-anti-identityᵣ {𝐹} = [≡]-intro
{-# REWRITE [==]-anti-identityᵣ #-}

[!=]-anti-identityᵣ : ∀{a} → (a != 𝑇 ≡ ! a)
[!=]-anti-identityᵣ {𝑇} = [≡]-intro
[!=]-anti-identityᵣ {𝐹} = [≡]-intro
{-# REWRITE [!=]-anti-identityᵣ #-}

---------------------------------------------
-- Left identities

[||]-identityₗ-raw : ∀{a} → (𝐹 || a ≡ a)
[||]-identityₗ-raw {𝑇} = [≡]-intro
[||]-identityₗ-raw {𝐹} = [≡]-intro
{-# REWRITE [||]-identityₗ-raw #-}
instance
  [||]-identityₗ : Identityₗ(_||_)(𝐹)
  Identityₗ.proof([||]-identityₗ) = [||]-identityₗ-raw

[&&]-identityₗ-raw : ∀{a} → (𝑇 && a ≡ a)
[&&]-identityₗ-raw {𝑇} = [≡]-intro
[&&]-identityₗ-raw {𝐹} = [≡]-intro
{-# REWRITE [&&]-identityₗ-raw #-}
instance
  [&&]-identityₗ : Identityₗ(_&&_)(𝑇)
  Identityₗ.proof([&&]-identityₗ) = [&&]-identityₗ-raw

[==]-identityₗ-raw : ∀{a} → (𝑇 == a ≡ a)
[==]-identityₗ-raw {𝑇} = [≡]-intro
[==]-identityₗ-raw {𝐹} = [≡]-intro
{-# REWRITE [==]-identityₗ-raw #-}
instance
  [==]-identityₗ : Identityₗ(_==_)(𝑇)
  Identityₗ.proof([==]-identityₗ) = [==]-identityₗ-raw

[!=]-identityₗ-raw : ∀{a} → (𝐹 != a ≡ a)
[!=]-identityₗ-raw {𝑇} = [≡]-intro
[!=]-identityₗ-raw {𝐹} = [≡]-intro
{-# REWRITE [!=]-identityₗ-raw #-}
instance
  [!=]-identityₗ : Identityₗ(_!=_)(𝐹)
  Identityₗ.proof([!=]-identityₗ) = [!=]-identityₗ-raw

---------------------------------------------
-- Left absorbers

[||]-absorberₗ-raw : ∀{a} → (𝑇 || a ≡ 𝑇)
[||]-absorberₗ-raw {𝑇} = [≡]-intro
[||]-absorberₗ-raw {𝐹} = [≡]-intro
{-# REWRITE [||]-absorberₗ-raw #-}
instance
  [||]-absorberₗ : Absorberₗ(_||_)(𝑇)
  Absorberₗ.proof([||]-absorberₗ) {a} = [||]-absorberₗ-raw {a}

[&&]-absorberₗ-raw : ∀{a} → (𝐹 && a ≡ 𝐹)
[&&]-absorberₗ-raw {𝑇} = [≡]-intro
[&&]-absorberₗ-raw {𝐹} = [≡]-intro
{-# REWRITE [&&]-absorberₗ-raw #-}
instance
  [&&]-absorberₗ : Absorberₗ(_&&_)(𝐹)
  Absorberₗ.proof([&&]-absorberₗ) {a} = [&&]-absorberₗ-raw {a}

---------------------------------------------
-- Right identities

[||]-identityᵣ-raw : ∀{a} → (a || 𝐹 ≡ a)
[||]-identityᵣ-raw {𝑇} = [≡]-intro
[||]-identityᵣ-raw {𝐹} = [≡]-intro
{-# REWRITE [||]-identityᵣ-raw #-}
instance
  [||]-identityᵣ : Identityᵣ(_||_)(𝐹)
  Identityᵣ.proof([||]-identityᵣ) = [||]-identityᵣ-raw

[&&]-identityᵣ-raw : ∀{a} → (a && 𝑇 ≡ a)
[&&]-identityᵣ-raw {𝑇} = [≡]-intro
[&&]-identityᵣ-raw {𝐹} = [≡]-intro
{-# REWRITE [&&]-identityᵣ-raw #-}
instance
  [&&]-identityᵣ : Identityᵣ(_&&_)(𝑇)
  Identityᵣ.proof([&&]-identityᵣ) = [&&]-identityᵣ-raw

[==]-identityᵣ-raw : ∀{a} → (a == 𝑇 ≡ a)
[==]-identityᵣ-raw {𝑇} = [≡]-intro
[==]-identityᵣ-raw {𝐹} = [≡]-intro
{-# REWRITE [==]-identityᵣ-raw #-}
instance
  [==]-identityᵣ : Identityᵣ(_==_)(𝑇)
  Identityᵣ.proof([==]-identityᵣ) = [==]-identityᵣ-raw

[!=]-identityᵣ-raw : ∀{a} → (a != 𝐹 ≡ a)
[!=]-identityᵣ-raw {𝑇} = [≡]-intro
[!=]-identityᵣ-raw {𝐹} = [≡]-intro
{-# REWRITE [!=]-identityᵣ-raw #-}
instance
  [!=]-identityᵣ : Identityᵣ(_!=_)(𝐹)
  Identityᵣ.proof([!=]-identityᵣ) = [!=]-identityᵣ-raw

---------------------------------------------
-- Identities

instance
  [||]-identity : Identity(_||_)(𝐹)
  [||]-identity = record{}

instance
  [&&]-identity : Identity(_&&_)(𝑇)
  [&&]-identity = record{}

instance
  [==]-identity : Identity(_==_)(𝑇)
  [==]-identity = record{}

instance
  [!=]-identity : Identity(_!=_)(𝐹)
  [!=]-identity = record{}

---------------------------------------------
-- Right absorbers

[||]-absorberᵣ-raw : ∀{a} → (a || 𝑇 ≡ 𝑇)
[||]-absorberᵣ-raw {𝑇} = [≡]-intro
[||]-absorberᵣ-raw {𝐹} = [≡]-intro
{-# REWRITE [||]-absorberᵣ-raw #-}
instance
  [||]-absorberᵣ : Absorberᵣ(_||_)(𝑇)
  Absorberᵣ.proof([||]-absorberᵣ) {a} = [||]-absorberᵣ-raw {a}

[&&]-absorberᵣ-raw : ∀{a} → (a && 𝐹 ≡ 𝐹)
[&&]-absorberᵣ-raw {𝑇} = [≡]-intro
[&&]-absorberᵣ-raw {𝐹} = [≡]-intro
{-# REWRITE [&&]-absorberᵣ-raw #-}
instance
  [&&]-absorberᵣ : Absorberᵣ(_&&_)(𝐹)
  Absorberᵣ.proof([&&]-absorberᵣ) {a} = [&&]-absorberᵣ-raw {a}

---------------------------------------------
-- Associativity

instance
  [||]-associativity : Associativity(_||_)
  Associativity.proof([||]-associativity) = proof where
    proof : Names.Associativity(_||_)
    proof {𝑇}{𝑇}{𝑇} = [≡]-intro
    proof {𝑇}{𝑇}{𝐹} = [≡]-intro
    proof {𝑇}{𝐹}{𝑇} = [≡]-intro
    proof {𝑇}{𝐹}{𝐹} = [≡]-intro
    proof {𝐹}{𝑇}{𝑇} = [≡]-intro
    proof {𝐹}{𝑇}{𝐹} = [≡]-intro
    proof {𝐹}{𝐹}{𝑇} = [≡]-intro
    proof {𝐹}{𝐹}{𝐹} = [≡]-intro

instance
  [&&]-associativity : Associativity(_&&_)
  Associativity.proof([&&]-associativity) = proof where
    proof : Names.Associativity(_&&_)
    proof {𝑇}{𝑇}{𝑇} = [≡]-intro
    proof {𝑇}{𝑇}{𝐹} = [≡]-intro
    proof {𝑇}{𝐹}{𝑇} = [≡]-intro
    proof {𝑇}{𝐹}{𝐹} = [≡]-intro
    proof {𝐹}{𝑇}{𝑇} = [≡]-intro
    proof {𝐹}{𝑇}{𝐹} = [≡]-intro
    proof {𝐹}{𝐹}{𝑇} = [≡]-intro
    proof {𝐹}{𝐹}{𝐹} = [≡]-intro

instance
  [==]-associativity : Associativity(_==_)
  Associativity.proof([==]-associativity) = proof where
    proof : Names.Associativity(_==_)
    proof {𝑇}{𝑇}{𝑇} = [≡]-intro
    proof {𝑇}{𝑇}{𝐹} = [≡]-intro
    proof {𝑇}{𝐹}{𝑇} = [≡]-intro
    proof {𝑇}{𝐹}{𝐹} = [≡]-intro
    proof {𝐹}{𝑇}{𝑇} = [≡]-intro
    proof {𝐹}{𝑇}{𝐹} = [≡]-intro
    proof {𝐹}{𝐹}{𝑇} = [≡]-intro
    proof {𝐹}{𝐹}{𝐹} = [≡]-intro

instance
  [!=]-associativity : Associativity(_!=_)
  Associativity.proof([!=]-associativity) = proof where
    proof : Names.Associativity(_!=_)
    proof {𝑇}{𝑇}{𝑇} = [≡]-intro
    proof {𝑇}{𝑇}{𝐹} = [≡]-intro
    proof {𝑇}{𝐹}{𝑇} = [≡]-intro
    proof {𝑇}{𝐹}{𝐹} = [≡]-intro
    proof {𝐹}{𝑇}{𝑇} = [≡]-intro
    proof {𝐹}{𝑇}{𝐹} = [≡]-intro
    proof {𝐹}{𝐹}{𝑇} = [≡]-intro
    proof {𝐹}{𝐹}{𝐹} = [≡]-intro

---------------------------------------------
-- Other

[⊼]-pseudo-associativity : (!(a ⊼ b) ⊼ c ≡ a ⊼ !(b ⊼ c))
[⊼]-pseudo-associativity {𝑇} {𝑇} {𝑇} = [≡]-intro
[⊼]-pseudo-associativity {𝑇} {𝑇} {𝐹} = [≡]-intro
[⊼]-pseudo-associativity {𝑇} {𝐹} {𝑇} = [≡]-intro
[⊼]-pseudo-associativity {𝑇} {𝐹} {𝐹} = [≡]-intro
[⊼]-pseudo-associativity {𝐹} {𝑇} {𝑇} = [≡]-intro
[⊼]-pseudo-associativity {𝐹} {𝑇} {𝐹} = [≡]-intro
[⊼]-pseudo-associativity {𝐹} {𝐹} {𝑇} = [≡]-intro
[⊼]-pseudo-associativity {𝐹} {𝐹} {𝐹} = [≡]-intro

[⊼]-to-conjunction : (!(a ⊼ b) ≡ a && b)
[⊼]-to-conjunction {𝑇} {𝑇} = [≡]-intro
[⊼]-to-conjunction {𝑇} {𝐹} = [≡]-intro
[⊼]-to-conjunction {𝐹} {𝑇} = [≡]-intro
[⊼]-to-conjunction {𝐹} {𝐹} = [≡]-intro

[⊼]-to-negation : (b ⊼ b ≡ ! b)
[⊼]-to-negation {𝑇} = [≡]-intro
[⊼]-to-negation {𝐹} = [≡]-intro

[⊼]-pseudo-absorptionₗ : (a ⊼ (a ⊼ b) ≡ a ⊼ (! b))
[⊼]-pseudo-absorptionₗ {𝑇} {𝑇} = [≡]-intro
[⊼]-pseudo-absorptionₗ {𝑇} {𝐹} = [≡]-intro
[⊼]-pseudo-absorptionₗ {𝐹} {𝑇} = [≡]-intro
[⊼]-pseudo-absorptionₗ {𝐹} {𝐹} = [≡]-intro

[⊼]-pseudo-absorptionᵣ : ((a ⊼ b) ⊼ b ≡ (! a) ⊼ b)
[⊼]-pseudo-absorptionᵣ {𝑇} {𝑇} = [≡]-intro
[⊼]-pseudo-absorptionᵣ {𝑇} {𝐹} = [≡]-intro
[⊼]-pseudo-absorptionᵣ {𝐹} {𝑇} = [≡]-intro
[⊼]-pseudo-absorptionᵣ {𝐹} {𝐹} = [≡]-intro

[⊼]-pseudo-pseudo-absorptionₗ : (((! a) ⊼ b) ⊼ (a ⊼ b) ≡ b)
[⊼]-pseudo-pseudo-absorptionₗ {𝑇} {𝑇} = [≡]-intro
[⊼]-pseudo-pseudo-absorptionₗ {𝑇} {𝐹} = [≡]-intro
[⊼]-pseudo-pseudo-absorptionₗ {𝐹} {𝑇} = [≡]-intro
[⊼]-pseudo-pseudo-absorptionₗ {𝐹} {𝐹} = [≡]-intro

[⊼]-pseudo-pseudo-absorptionᵣ : ((a ⊼ (! b)) ⊼ (a ⊼ b) ≡ a)
[⊼]-pseudo-pseudo-absorptionᵣ {𝑇} {𝑇} = [≡]-intro
[⊼]-pseudo-pseudo-absorptionᵣ {𝑇} {𝐹} = [≡]-intro
[⊼]-pseudo-pseudo-absorptionᵣ {𝐹} {𝑇} = [≡]-intro
[⊼]-pseudo-pseudo-absorptionᵣ {𝐹} {𝐹} = [≡]-intro

[⊽]-pseudo-associativity : (!(a ⊽ b) ⊽ c ≡ a ⊽ !(b ⊽ c))
[⊽]-pseudo-associativity {𝑇} {𝑇} {𝑇} = [≡]-intro
[⊽]-pseudo-associativity {𝑇} {𝑇} {𝐹} = [≡]-intro
[⊽]-pseudo-associativity {𝑇} {𝐹} {𝑇} = [≡]-intro
[⊽]-pseudo-associativity {𝑇} {𝐹} {𝐹} = [≡]-intro
[⊽]-pseudo-associativity {𝐹} {𝑇} {𝑇} = [≡]-intro
[⊽]-pseudo-associativity {𝐹} {𝑇} {𝐹} = [≡]-intro
[⊽]-pseudo-associativity {𝐹} {𝐹} {𝑇} = [≡]-intro
[⊽]-pseudo-associativity {𝐹} {𝐹} {𝐹} = [≡]-intro

[⊽]-to-disjunction : (!(a ⊽ b) ≡ a || b)
[⊽]-to-disjunction {𝑇} {𝑇} = [≡]-intro
[⊽]-to-disjunction {𝑇} {𝐹} = [≡]-intro
[⊽]-to-disjunction {𝐹} {𝑇} = [≡]-intro
[⊽]-to-disjunction {𝐹} {𝐹} = [≡]-intro

[⊽]-to-negation : (b ⊽ b ≡ ! b)
[⊽]-to-negation {𝑇} = [≡]-intro
[⊽]-to-negation {𝐹} = [≡]-intro

[⊽]-pseudo-absorptionₗ : (a ⊽ (a ⊽ b) ≡ a ⊽ (! b))
[⊽]-pseudo-absorptionₗ {𝑇} {𝑇} = [≡]-intro
[⊽]-pseudo-absorptionₗ {𝑇} {𝐹} = [≡]-intro
[⊽]-pseudo-absorptionₗ {𝐹} {𝑇} = [≡]-intro
[⊽]-pseudo-absorptionₗ {𝐹} {𝐹} = [≡]-intro

[⊽]-pseudo-absorptionᵣ : ((a ⊽ b) ⊽ b ≡ (! a) ⊽ b)
[⊽]-pseudo-absorptionᵣ {𝑇} {𝑇} = [≡]-intro
[⊽]-pseudo-absorptionᵣ {𝑇} {𝐹} = [≡]-intro
[⊽]-pseudo-absorptionᵣ {𝐹} {𝑇} = [≡]-intro
[⊽]-pseudo-absorptionᵣ {𝐹} {𝐹} = [≡]-intro

[⊽]-pseudo-pseudo-absorptionₗ : (((! a) ⊽ b) ⊽ (a ⊽ b) ≡ b)
[⊽]-pseudo-pseudo-absorptionₗ {𝑇} {𝑇} = [≡]-intro
[⊽]-pseudo-pseudo-absorptionₗ {𝑇} {𝐹} = [≡]-intro
[⊽]-pseudo-pseudo-absorptionₗ {𝐹} {𝑇} = [≡]-intro
[⊽]-pseudo-pseudo-absorptionₗ {𝐹} {𝐹} = [≡]-intro

[⊽]-pseudo-pseudo-absorptionᵣ : ((a ⊽ (! b)) ⊽ (a ⊽ b) ≡ a)
[⊽]-pseudo-pseudo-absorptionᵣ {𝑇} {𝑇} = [≡]-intro
[⊽]-pseudo-pseudo-absorptionᵣ {𝑇} {𝐹} = [≡]-intro
[⊽]-pseudo-pseudo-absorptionᵣ {𝐹} {𝑇} = [≡]-intro
[⊽]-pseudo-pseudo-absorptionᵣ {𝐹} {𝐹} = [≡]-intro

---------------------------------------------
-- Commutativity

instance
  [||]-commutativity : Commutativity(_||_)
  Commutativity.proof([||]-commutativity) = proof where
    proof : Names.Commutativity(_||_)
    proof {𝑇}{𝑇} = [≡]-intro
    proof {𝑇}{𝐹} = [≡]-intro
    proof {𝐹}{𝑇} = [≡]-intro
    proof {𝐹}{𝐹} = [≡]-intro

instance
  [&&]-commutativity : Commutativity(_&&_)
  Commutativity.proof([&&]-commutativity) = proof where
    proof : Names.Commutativity(_&&_)
    proof {𝑇}{𝑇} = [≡]-intro
    proof {𝑇}{𝐹} = [≡]-intro
    proof {𝐹}{𝑇} = [≡]-intro
    proof {𝐹}{𝐹} = [≡]-intro

instance
  [==]-commutativity : Commutativity(_==_)
  Commutativity.proof([==]-commutativity) = proof where
    proof : Names.Commutativity(_==_)
    proof {𝑇}{𝑇} = [≡]-intro
    proof {𝑇}{𝐹} = [≡]-intro
    proof {𝐹}{𝑇} = [≡]-intro
    proof {𝐹}{𝐹} = [≡]-intro

instance
  [!=]-commutativity : Commutativity(_!=_)
  Commutativity.proof([!=]-commutativity) = proof where
    proof : Names.Commutativity(_!=_)
    proof {𝑇}{𝑇} = [≡]-intro
    proof {𝑇}{𝐹} = [≡]-intro
    proof {𝐹}{𝑇} = [≡]-intro
    proof {𝐹}{𝐹} = [≡]-intro

instance
  [⊼]-commutativity : Commutativity(_⊼_)
  Commutativity.proof([⊼]-commutativity) = proof where
    proof : Names.Commutativity(_⊼_)
    proof {𝑇}{𝑇} = [≡]-intro
    proof {𝑇}{𝐹} = [≡]-intro
    proof {𝐹}{𝑇} = [≡]-intro
    proof {𝐹}{𝐹} = [≡]-intro

instance
  [⊽]-commutativity : Commutativity(_⊽_)
  Commutativity.proof([⊽]-commutativity) = proof where
    proof : Names.Commutativity(_⊽_)
    proof {𝑇}{𝑇} = [≡]-intro
    proof {𝑇}{𝐹} = [≡]-intro
    proof {𝐹}{𝑇} = [≡]-intro
    proof {𝐹}{𝐹} = [≡]-intro

instance
  [⊕]-commutativity : Commutativity(_⊕_)
  Commutativity.proof([⊕]-commutativity) = proof where
    proof : Names.Commutativity(_⊕_)
    proof {𝑇}{𝑇} = [≡]-intro
    proof {𝑇}{𝐹} = [≡]-intro
    proof {𝐹}{𝑇} = [≡]-intro
    proof {𝐹}{𝐹} = [≡]-intro

instance
  [&&][||]-distributivityₗ : Distributivityₗ(_&&_)(_||_)
  Distributivityₗ.proof([&&][||]-distributivityₗ) = proof where
    proof : Names.Distributivityₗ(_&&_)(_||_)
    proof {𝑇}{𝑇}{𝑇} = [≡]-intro
    proof {𝑇}{𝑇}{𝐹} = [≡]-intro
    proof {𝑇}{𝐹}{𝑇} = [≡]-intro
    proof {𝑇}{𝐹}{𝐹} = [≡]-intro
    proof {𝐹}{𝑇}{𝑇} = [≡]-intro
    proof {𝐹}{𝑇}{𝐹} = [≡]-intro
    proof {𝐹}{𝐹}{𝑇} = [≡]-intro
    proof {𝐹}{𝐹}{𝐹} = [≡]-intro

instance
  [||][&&]-distributivityₗ : Distributivityₗ(_||_)(_&&_)
  Distributivityₗ.proof([||][&&]-distributivityₗ) = proof where
    proof : Names.Distributivityₗ(_||_)(_&&_)
    proof {𝑇}{𝑇}{𝑇} = [≡]-intro
    proof {𝑇}{𝑇}{𝐹} = [≡]-intro
    proof {𝑇}{𝐹}{𝑇} = [≡]-intro
    proof {𝑇}{𝐹}{𝐹} = [≡]-intro
    proof {𝐹}{𝑇}{𝑇} = [≡]-intro
    proof {𝐹}{𝑇}{𝐹} = [≡]-intro
    proof {𝐹}{𝐹}{𝑇} = [≡]-intro
    proof {𝐹}{𝐹}{𝐹} = [≡]-intro

instance
  [||]-oppositeFunctionₗ : ComplementFunctionₗ(_||_)(!)
  ComplementFunctionₗ.proof([||]-oppositeFunctionₗ) = proof where
    proof : Names.InverseFunctionₗ(_||_)(𝑇)(!)
    proof {𝑇} = [≡]-intro
    proof {𝐹} = [≡]-intro

instance
  [||]-oppositeFunctionᵣ : ComplementFunctionᵣ(_||_)(!)
  ComplementFunctionᵣ.proof([||]-oppositeFunctionᵣ) = proof where
    proof : Names.InverseFunctionᵣ(_||_)(𝑇)(!)
    proof {𝑇} = [≡]-intro
    proof {𝐹} = [≡]-intro

instance
  [&&]-oppositeFunctionₗ : ComplementFunctionₗ(_&&_)(!)
  ComplementFunctionₗ.proof([&&]-oppositeFunctionₗ) = proof where
    proof : Names.InverseFunctionₗ(_&&_)(𝐹)(!)
    proof {𝑇} = [≡]-intro
    proof {𝐹} = [≡]-intro

instance
  [&&]-oppositeFunctionᵣ : ComplementFunctionᵣ(_&&_)(!)
  ComplementFunctionᵣ.proof([&&]-oppositeFunctionᵣ) = proof where
    proof : Names.InverseFunctionᵣ(_&&_)(𝐹)(!)
    proof {𝑇} = [≡]-intro
    proof {𝐹} = [≡]-intro

---------------------------------------------
-- Algebraic structures

instance
  [&&]-monoid : Monoid(_&&_)
  [&&]-monoid = record{}

instance
  [||]-monoid : Monoid(_||_)
  [||]-monoid = record{}

instance
  [==]-monoid : Monoid(_==_)
  [==]-monoid = record{}

instance
  [!=]-monoid : Monoid(_!=_)
  [!=]-monoid = record{}

-- TODO: Set algebra

---------------------------------------------
-- Inverting

inverted-[==][!=] : ∀{a b} → (!(a == b) ≡ (a != b))
inverted-[==][!=] {𝑇}{𝑇} = [≡]-intro
inverted-[==][!=] {𝑇}{𝐹} = [≡]-intro
inverted-[==][!=] {𝐹}{𝑇} = [≡]-intro
inverted-[==][!=] {𝐹}{𝐹} = [≡]-intro

inverted-[!=][==] : ∀{a b} → (!(a != b) ≡ (a == b))
inverted-[!=][==] {𝑇}{𝑇} = [≡]-intro
inverted-[!=][==] {𝑇}{𝐹} = [≡]-intro
inverted-[!=][==] {𝐹}{𝑇} = [≡]-intro
inverted-[!=][==] {𝐹}{𝐹} = [≡]-intro

---------------------------------------------
-- Rules of classical logic

-- A boolean operation is either true or false
bivalence : ∀{a} → ((a ≡ 𝑇) ∨ (a ≡ 𝐹))
bivalence {𝑇} = Logic.[∨]-introₗ [≡]-intro
bivalence {𝐹} = Logic.[∨]-introᵣ [≡]-intro

-- A boolean operation is not both true and false at the same time
disjointness : ∀{a} → ¬((a ≡ 𝑇) ∧ (a ≡ 𝐹))
disjointness {𝑇} (Logic.[∧]-intro [≡]-intro ())
disjointness {𝐹} (Logic.[∧]-intro () [≡]-intro)

[→?]-disjunctive-form : ∀{a b} → ((a →? b) ≡ ((! a) || b))
[→?]-disjunctive-form {𝑇} {𝑇} = [≡]-intro
[→?]-disjunctive-form {𝑇} {𝐹} = [≡]-intro
[→?]-disjunctive-form {𝐹} {𝑇} = [≡]-intro
[→?]-disjunctive-form {𝐹} {𝐹} = [≡]-intro

[==]-disjunctive-form : ∀{a b} → ((a == b) ≡ ((a && b) || ((! a) && (! b))))
[==]-disjunctive-form {𝑇} {𝑇} = [≡]-intro
[==]-disjunctive-form {𝑇} {𝐹} = [≡]-intro
[==]-disjunctive-form {𝐹} {𝑇} = [≡]-intro
[==]-disjunctive-form {𝐹} {𝐹} = [≡]-intro

module 𝑇 where
  [∧]-intro : ∀{a b} → (a ≡ 𝑇) → (b ≡ 𝑇) → ((a && b) ≡ 𝑇)
  [∧]-intro [≡]-intro [≡]-intro = [≡]-intro

  [∨]-introₗ : ∀{a b} → (a ≡ 𝑇) → ((a || b) ≡ 𝑇)
  [∨]-introₗ {_}{𝑇} [≡]-intro = [≡]-intro
  [∨]-introₗ {_}{𝐹} [≡]-intro = [≡]-intro

  [∨]-introᵣ : ∀{a b} → (b ≡ 𝑇) → ((a || b) ≡ 𝑇)
  [∨]-introᵣ {𝑇}{_} [≡]-intro = [≡]-intro
  [∨]-introᵣ {𝐹}{_} [≡]-intro = [≡]-intro

  [∧]-elimₗ : ∀{a b} → ((a && b) ≡ 𝑇) → (a ≡ 𝑇)
  [∧]-elimₗ {𝑇}{𝑇} [≡]-intro = [≡]-intro
  [∧]-elimₗ {𝑇}{𝐹} ()
  [∧]-elimₗ {𝐹}{𝑇} ()
  [∧]-elimₗ {𝐹}{𝐹} ()

  [∧]-elimᵣ : ∀{a b} → ((a && b) ≡ 𝑇) → (b ≡ 𝑇)
  [∧]-elimᵣ {𝑇}{𝑇} [≡]-intro = [≡]-intro
  [∧]-elimᵣ {𝑇}{𝐹} ()
  [∧]-elimᵣ {𝐹}{𝑇} ()
  [∧]-elimᵣ {𝐹}{𝐹} ()

  [∨]-elim : ∀{a b}{ℓ₂}{φ : Type{ℓ₂}} → ((a ≡ 𝑇) → φ) → ((b ≡ 𝑇) → φ) → ((a || b) ≡ 𝑇) → φ
  [∨]-elim {𝑇}{𝑇}{_} f _ [≡]-intro = f [≡]-intro
  [∨]-elim {𝑇}{𝐹}{_} f _ [≡]-intro = f [≡]-intro
  [∨]-elim {𝐹}{𝑇}{_} _ f [≡]-intro = f [≡]-intro
  [∨]-elim {𝐹}{𝐹}{_} _ f ()

  [¬]-intro : ∀{a} → (a ≡ 𝐹) → (! a ≡ 𝑇)
  [¬]-intro [≡]-intro = [≡]-intro

  [¬]-elim : ∀{a} → (! a ≡ 𝑇) → (a ≡ 𝐹)
  [¬]-elim {𝑇} ()
  [¬]-elim {𝐹} [≡]-intro = [≡]-intro

  [¬¬]-elim : ∀{a} → (!(! a) ≡ 𝑇) → (a ≡ 𝑇)
  [¬¬]-elim {𝑇} [≡]-intro = [≡]-intro
  [¬¬]-elim {𝐹} ()

  preserves-[&&][∧] : ∀{a b} → ((a && b) ≡ 𝑇) ↔ (a ≡ 𝑇)∧(b ≡ 𝑇)
  preserves-[&&][∧] = [↔]-intro
    (\{(Logic.[∧]-intro l r) → [∧]-intro l r})
    (proof ↦ Logic.[∧]-intro ([∧]-elimₗ proof) ([∧]-elimᵣ proof))

  preserves-[||][∨] : ∀{a b} → ((a || b) ≡ 𝑇) ↔ (a ≡ 𝑇)∨(b ≡ 𝑇)
  preserves-[||][∨] = [↔]-intro
    (Logic.[∨]-elim [∨]-introₗ [∨]-introᵣ)
    ([∨]-elim Logic.[∨]-introₗ Logic.[∨]-introᵣ)

  preserves-[!][¬] : ∀{a} → (! a ≡ 𝑇) ↔ ¬(a ≡ 𝑇)
  preserves-[!][¬] {a} = [↔]-intro (l{a}) (r{a}) where
    l : ∀{a} → (! a ≡ 𝑇) ← ¬(a ≡ 𝑇)
    l {𝐹} _ = [≡]-intro
    l {𝑇} f = [⊥]-elim (f [≡]-intro)

    r : ∀{a} → (! a ≡ 𝑇) → ¬(a ≡ 𝑇)
    r {𝑇} () _
    r {𝐹} _ ()

  [≡]-transfer : ∀{a b} → ((a == b) ≡ 𝑇) ↔ (a ≡ b)
  [≡]-transfer {𝑇}{𝑇} = [↔]-intro (_ ↦ [≡]-intro) (_ ↦ [≡]-intro)
  [≡]-transfer {𝐹}{𝑇} = [↔]-intro (\()) (\())
  [≡]-transfer {𝑇}{𝐹} = [↔]-intro (\()) (\())
  [≡]-transfer {𝐹}{𝐹} = [↔]-intro (_ ↦ [≡]-intro) (_ ↦ [≡]-intro)

  [≢]-transfer : ∀{a b} → ((a != b) ≡ 𝑇) ↔ (a ≢ b)
  [≢]-transfer {𝑇}{𝑇} = [↔]-intro (ab ↦ [⊥]-elim(ab [≡]-intro)) (\())
  [≢]-transfer {𝐹}{𝑇} = [↔]-intro (_ ↦ [≡]-intro) (_ ↦ \())
  [≢]-transfer {𝑇}{𝐹} = [↔]-intro (_ ↦ [≡]-intro) (_ ↦ \())
  [≢]-transfer {𝐹}{𝐹} = [↔]-intro (ab ↦ [⊥]-elim(ab [≡]-intro)) (\())

module 𝐹 where
  [∧]-introₗ : ∀{a b} → (a ≡ 𝐹) → ((a && b) ≡ 𝐹)
  [∧]-introₗ {_}{𝑇} [≡]-intro = [≡]-intro
  [∧]-introₗ {_}{𝐹} [≡]-intro = [≡]-intro

  [∧]-introᵣ : ∀{a b} → (b ≡ 𝐹) → ((a && b) ≡ 𝐹)
  [∧]-introᵣ {𝑇}{_} [≡]-intro = [≡]-intro
  [∧]-introᵣ {𝐹}{_} [≡]-intro = [≡]-intro

  [∨]-intro : ∀{a b} → (a ≡ 𝐹) → (b ≡ 𝐹) → ((a || b) ≡ 𝐹)
  [∨]-intro [≡]-intro [≡]-intro = [≡]-intro

  [¬]-intro : ∀{a} → (! a ≡ 𝑇) → (a ≡ 𝐹)
  [¬]-intro = 𝑇.[¬]-elim

  [¬]-elim : ∀{a} → (a ≡ 𝐹) → (! a ≡ 𝑇)
  [¬]-elim = 𝑇.[¬]-intro

[≢][𝑇]-is-[𝐹] : ∀{a} → (a ≢ 𝑇) ↔ (a ≡ 𝐹)
[≢][𝑇]-is-[𝐹] {a} = [↔]-intro (l{a}) (r{a}) where
  r : ∀{a} → (a ≢ 𝑇) → (a ≡ 𝐹)
  r {𝑇} (a≢𝑇) = [⊥]-elim ((a≢𝑇) ([≡]-intro))
  r {𝐹} (a≢𝑇) = [≡]-intro

  l : ∀{a} → (a ≢ 𝑇) ← (a ≡ 𝐹)
  l {𝑇} ()
  l {𝐹} (a≡𝐹) ()

[≢][𝐹]-is-[𝑇] : ∀{a} → (a ≢ 𝐹) ↔ (a ≡ 𝑇)
[≢][𝐹]-is-[𝑇] {a} = [↔]-intro (l{a}) (r{a}) where
  r : ∀{a} → (a ≢ 𝐹) → (a ≡ 𝑇)
  r {𝑇} (a≢𝐹) = [≡]-intro
  r {𝐹} (a≢𝐹) = [⊥]-elim ((a≢𝐹) ([≡]-intro))

  l : ∀{a} → (a ≢ 𝐹) ← (a ≡ 𝑇)
  l {𝑇} (a≡𝑇) ()
  l {𝐹} ()

---------------------------------------------
-- If-statements

module _ {ℓ₁ ℓ₂} {T : Type{ℓ₁}} {x y : T} {P : T → Type{ℓ₂}} where
  if-intro : ∀{B} → ((B ≡ 𝑇) → P(x)) → ((B ≡ 𝐹) → P(y)) → P(if B then x else y)
  if-intro {𝑇} px py = px [≡]-intro
  if-intro {𝐹} px py = py [≡]-intro

module _ {ℓ₁ ℓ₂ ℓ₃} {T : Type{ℓ₁}} {x y : T} {P : T → Type{ℓ₂}} {Q : Bool → Type{ℓ₃}} where
  if-elim : ∀{B} → P(if B then x else y) → (P(x) → Q(𝑇)) → (P(y) → Q(𝐹)) → Q(B)
  if-elim{𝑇} p pxq pyq = pxq p
  if-elim{𝐹} p pxq pyq = pyq p

module _ {ℓ₁ ℓ₂ ℓ₃} {T : Type{ℓ₁}} {x y : T} {P : T → Type{ℓ₂}} {Q : Type{ℓ₃}} where
  if-bool-elim : ∀{B} → P(if B then x else y) → (P(x) → (B ≡ 𝑇) → Q) → (P(y) → (B ≡ 𝐹) → Q) → Q
  if-bool-elim{𝑇} p pxq pyq = pxq p [≡]-intro
  if-bool-elim{𝐹} p pxq pyq = pyq p [≡]-intro

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {T : Type{ℓ₁}} {P : T → Type{ℓ₂}} {X : Type{ℓ₃}} {Y : Type{ℓ₄}} (nxy : X → Y → Logic.⊥) where
  either-bool-left : (xy : (X ∨ Y)) → (X ↔ (Either.isRight(xy) ≡ 𝐹))
  either-bool-left xy with bivalence{Either.isRight(xy)}
  either-bool-left (Left  x) | Right f = [↔]-intro (const x) (const f)
  either-bool-left (Right y) | Left  t = [↔]-intro (\()) (x ↦ empty(nxy x y))

  either-bool-right : (xy : (X ∨ Y)) → (Y ↔ (Either.isRight(xy) ≡ 𝑇))
  either-bool-right xy with bivalence{Either.isRight(xy)}
  either-bool-right (Left  x) | Right f = [↔]-intro (\()) (y ↦ empty(nxy x y))
  either-bool-right (Right y) | Left  t = [↔]-intro (const y) (const t)

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {T : Type{ℓ₁}} {P : T → Type{ℓ₂}} {X : Type{ℓ₃}} {Y : Type{ℓ₄}} where
  either-bool-leftₗ : (xy : (X ∨ Y)) → (X ← (Either.isRight(xy) ≡ 𝐹))
  either-bool-leftₗ xy with bivalence{Either.isRight(xy)}
  either-bool-leftₗ (Left  x) | Right f = const x
  either-bool-leftₗ (Right y) | Left  t = \()

  either-bool-rightₗ : (xy : (X ∨ Y)) → (Y ← (Either.isRight(xy) ≡ 𝑇))
  either-bool-rightₗ xy with bivalence{Either.isRight(xy)}
  either-bool-rightₗ (Left  x) | Right f = \()
  either-bool-rightₗ (Right y) | Left  t = const y

  if-not-either-bool-intro : ∀{x y : T} → (X → P(x)) → (Y → P(y)) → (xy : (X ∨ Y)) → P(if not(Either.isRight(xy)) then x else y)
  if-not-either-bool-intro {x}{y} xp yp xy = if-intro {x = x}{y = y} (xp ∘ either-bool-leftₗ xy ∘ 𝑇.[¬]-elim) (yp ∘ either-bool-rightₗ xy ∘ 𝑇.[¬¬]-elim ∘ 𝐹.[¬]-elim)

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {T : Type{ℓ₁}} {P : T → Type{ℓ₂}} {X : Type{ℓ₃}} {Y : Type{ℓ₄}} where
  if-either-bool-intro : ∀{x y : T} → (X → P(x)) → (Y → P(y)) → (xy : (X ∨ Y)) → P(if Either.isRight(xy) then y else x)
  if-either-bool-intro {x}{y} xp yp xy = if-intro {x = y}{y = x} (yp ∘ either-bool-rightₗ {P = P} xy) (xp ∘ either-bool-leftₗ {P = P} xy)

---------------------------------------------
-- The predicate of if-statements

module _ {ℓ} {T : Type{ℓ}} {x y : T} where
  if-and : ∀{B₁ B₂} → (if (B₁ && B₂) then x else y ≡ if B₁ then (if B₂ then x else y) else y)
  if-and {𝐹}{𝐹} = [≡]-intro
  if-and {𝐹}{𝑇} = [≡]-intro
  if-and {𝑇}{𝐹} = [≡]-intro
  if-and {𝑇}{𝑇} = [≡]-intro

  if-or : ∀{B₁ B₂} → (if (B₁ || B₂) then x else y ≡ if B₁ then x else if B₂ then x else y)
  if-or {𝐹}{𝐹} = [≡]-intro
  if-or {𝐹}{𝑇} = [≡]-intro
  if-or {𝑇}{𝐹} = [≡]-intro
  if-or {𝑇}{𝑇} = [≡]-intro

  if-not : ∀{B} → (if (! B) then x else y ≡ if B then y else x)
  if-not {𝐹} = [≡]-intro
  if-not {𝑇} = [≡]-intro

---------------------------------------------
-- The results of if-statements

module _ {ℓ} {T : Type{ℓ}} {x : T} {B} where
  if-then-redundant : (if B then x else x ≡ x)
  if-then-redundant = elim-redundant{b = B}

module _ {ℓ} {T : Type{ℓ}} {B} where
  if-then-bool-inverse : (if B then 𝑇 else 𝐹 ≡ B)
  if-then-bool-inverse = elim-inverse{b = B}

  if-then-bool-anti-inverse : (if B then 𝐹 else 𝑇 ≡ ! B)
  if-then-bool-anti-inverse = elim-anti-inverse{b = B}
