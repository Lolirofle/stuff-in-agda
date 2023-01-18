module Numeral.Charge.Proofs where

open import Logic.IntroInstances
open import Numeral.Charge
open import Numeral.Charge.Oper
open import Relator.Equals
open import Relator.Equals.Proofs.Equivalence
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Setoid hiding (_≡_ ; _≢_)
open import Type

instance
  Charge-equiv : Equiv(Charge)
  Charge-equiv = [≡]-equiv

instance
  [+]-identityₗ : Identityₗ(_+_)(𝟎)
  Identityₗ.proof [+]-identityₗ {➕} = [≡]-intro
  Identityₗ.proof [+]-identityₗ {𝟎} = [≡]-intro
  Identityₗ.proof [+]-identityₗ {➖} = [≡]-intro

instance
  [+]-identityᵣ : Identityᵣ(_+_)(𝟎)
  Identityᵣ.proof [+]-identityᵣ {➕} = [≡]-intro
  Identityᵣ.proof [+]-identityᵣ {𝟎} = [≡]-intro
  Identityᵣ.proof [+]-identityᵣ {➖} = [≡]-intro

instance
  [+]-identity : Identity(_+_)(𝟎)
  [+]-identity = intro

instance
  [+]-inverseFunctionₗ : InverseFunctionₗ(_+_)(−_)
  InverseFunctionₗ.proof [+]-inverseFunctionₗ {➕} = [≡]-intro
  InverseFunctionₗ.proof [+]-inverseFunctionₗ {𝟎} = [≡]-intro
  InverseFunctionₗ.proof [+]-inverseFunctionₗ {➖} = [≡]-intro

instance
  [+]-inverseFunctionᵣ : InverseFunctionᵣ(_+_)(−_)
  InverseFunctionᵣ.proof [+]-inverseFunctionᵣ {➕} = [≡]-intro
  InverseFunctionᵣ.proof [+]-inverseFunctionᵣ {𝟎} = [≡]-intro
  InverseFunctionᵣ.proof [+]-inverseFunctionᵣ {➖} = [≡]-intro

instance
  [+]-inverseFunction : InverseFunction(_+_)(−_)
  [+]-inverseFunction = intro

instance
  [⨯]-commutativity : Commutativity(_⨯_)
  Commutativity.proof [⨯]-commutativity {➕} {➕} = [≡]-intro
  Commutativity.proof [⨯]-commutativity {➕} {𝟎} = [≡]-intro
  Commutativity.proof [⨯]-commutativity {➕} {➖} = [≡]-intro
  Commutativity.proof [⨯]-commutativity {𝟎} {➕} = [≡]-intro
  Commutativity.proof [⨯]-commutativity {𝟎} {𝟎} = [≡]-intro
  Commutativity.proof [⨯]-commutativity {𝟎} {➖} = [≡]-intro
  Commutativity.proof [⨯]-commutativity {➖} {➕} = [≡]-intro
  Commutativity.proof [⨯]-commutativity {➖} {𝟎} = [≡]-intro
  Commutativity.proof [⨯]-commutativity {➖} {➖} = [≡]-intro

instance
  [⨯]-associativity : Associativity(_⨯_)
  Associativity.proof [⨯]-associativity {➕} {➕} {➕} = [≡]-intro
  Associativity.proof [⨯]-associativity {➕} {➕} {𝟎} = [≡]-intro
  Associativity.proof [⨯]-associativity {➕} {➕} {➖} = [≡]-intro
  Associativity.proof [⨯]-associativity {➕} {𝟎} {➕} = [≡]-intro
  Associativity.proof [⨯]-associativity {➕} {𝟎} {𝟎} = [≡]-intro
  Associativity.proof [⨯]-associativity {➕} {𝟎} {➖} = [≡]-intro
  Associativity.proof [⨯]-associativity {➕} {➖} {➕} = [≡]-intro
  Associativity.proof [⨯]-associativity {➕} {➖} {𝟎} = [≡]-intro
  Associativity.proof [⨯]-associativity {➕} {➖} {➖} = [≡]-intro
  Associativity.proof [⨯]-associativity {𝟎} {➕} {➕} = [≡]-intro
  Associativity.proof [⨯]-associativity {𝟎} {➕} {𝟎} = [≡]-intro
  Associativity.proof [⨯]-associativity {𝟎} {➕} {➖} = [≡]-intro
  Associativity.proof [⨯]-associativity {𝟎} {𝟎} {➕} = [≡]-intro
  Associativity.proof [⨯]-associativity {𝟎} {𝟎} {𝟎} = [≡]-intro
  Associativity.proof [⨯]-associativity {𝟎} {𝟎} {➖} = [≡]-intro
  Associativity.proof [⨯]-associativity {𝟎} {➖} {➕} = [≡]-intro
  Associativity.proof [⨯]-associativity {𝟎} {➖} {𝟎} = [≡]-intro
  Associativity.proof [⨯]-associativity {𝟎} {➖} {➖} = [≡]-intro
  Associativity.proof [⨯]-associativity {➖} {➕} {➕} = [≡]-intro
  Associativity.proof [⨯]-associativity {➖} {➕} {𝟎} = [≡]-intro
  Associativity.proof [⨯]-associativity {➖} {➕} {➖} = [≡]-intro
  Associativity.proof [⨯]-associativity {➖} {𝟎} {➕} = [≡]-intro
  Associativity.proof [⨯]-associativity {➖} {𝟎} {𝟎} = [≡]-intro
  Associativity.proof [⨯]-associativity {➖} {𝟎} {➖} = [≡]-intro
  Associativity.proof [⨯]-associativity {➖} {➖} {➕} = [≡]-intro
  Associativity.proof [⨯]-associativity {➖} {➖} {𝟎} = [≡]-intro
  Associativity.proof [⨯]-associativity {➖} {➖} {➖} = [≡]-intro

instance
  [⨯]-absorberₗ : Absorberₗ(_⨯_)(𝟎)
  Absorberₗ.proof [⨯]-absorberₗ {➕} = [≡]-intro
  Absorberₗ.proof [⨯]-absorberₗ {𝟎} = [≡]-intro
  Absorberₗ.proof [⨯]-absorberₗ {➖} = [≡]-intro

instance
  [⨯]-absorberᵣ : Absorberᵣ(_⨯_)(𝟎)
  Absorberᵣ.proof [⨯]-absorberᵣ {➕} = [≡]-intro
  Absorberᵣ.proof [⨯]-absorberᵣ {𝟎} = [≡]-intro
  Absorberᵣ.proof [⨯]-absorberᵣ {➖} = [≡]-intro

instance
  [⨯]-absorber : Absorber(_⨯_)(𝟎)
  [⨯]-absorber = intro

elim₃-const : ∀{ℓ}{T : Type{ℓ}}{c : T}{s} → (elim₃ c c c s ≡ c)
elim₃-const {s = ➕} = [≡]-intro
elim₃-const {s = 𝟎}  = [≡]-intro
elim₃-const {s = ➖} = [≡]-intro
