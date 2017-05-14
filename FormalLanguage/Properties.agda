module FormalLanguage.Properties where

import Level as Lvl
open import FormalLanguage
open import Logic.Propositional{Lvl.𝟎}
open import Relator.Equals{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Operator.Properties{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Operator.SetAlgebra{Lvl.𝟎}{Lvl.𝟎}
open import Structure.Function.Domain{Lvl.𝟎}{Lvl.𝟎}

-- TODO: Prove all these

module _ {∑}{s} where
  private _𝁼_ = Oper._𝁼_ {∑}{s}
  private _∪_ = Oper._∪_ {∑}{s}
  private _∩_ = Oper._∩_ {∑}{s}
  private ε   = Oper.ε {∑}{s}
  private ∅   = Oper.∅ {∑}{s}
  private _*   = Oper._* {∑}{s}

  postulate [𝁼]-associativity : Associativity(_𝁼_)
  postulate [𝁼]-distributivityₗ : Distributivityₗ(_𝁼_)(_∪_)
  postulate [𝁼]-distributivityᵣ : Distributivityᵣ(_𝁼_)(_∪_)
  postulate [𝁼]-identityₗ : Identityₗ(_𝁼_)(ε)
  postulate [𝁼]-identityᵣ : Identityᵣ(_𝁼_)(ε)
  postulate [𝁼]-absorberₗ : Absorberₗ(_𝁼_)(∅)
  postulate [𝁼]-absorberᵣ : Absorberᵣ(_𝁼_)(∅)
  postulate [*]-fixpoint-[ε] : FixPoint(_*)(ε)
  postulate [*]-on-[∅] : (∅ * ≡ ε)
  postulate [*]-on-[*] : ∀{L} → ((L *)* ≡ L *)
  postulate [𝁼]-commutativity-with-[*] : ∀{L} → ((L *) 𝁼 L ≡ L 𝁼 (L *))
  -- postulate [𝁼]-set-algebra : SetAlgebra -- TODO: Complement is missing

-- TODO: Set properties
-- TODO: Connection with logic (from sets) in relations
