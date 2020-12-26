module Numeral.Sign.Proofs where

open import Logic.IntroInstances
open import Numeral.Sign
open import Numeral.Sign.Oper
open import Numeral.Sign.Oper0 renaming (_+_ to _+₀_ ; _⨯_ to _⨯₀_ ; −_ to −₀_)
open import Relator.Equals
open import Relator.Equals.Proofs.Equivalence
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Setoid hiding (_≢_)

instance
  [−|+]-equiv : Equiv(−|+)
  [−|+]-equiv = [≡]-equiv

instance
  [−|0|+]-equiv : Equiv(−|0|+)
  [−|0|+]-equiv = [≡]-equiv

instance
  [+]-commutativity : Commutativity(_+_)
  Commutativity.proof [+]-commutativity {➕} {➕} = [≡]-intro
  Commutativity.proof [+]-commutativity {➕} {➖} = [≡]-intro
  Commutativity.proof [+]-commutativity {➖} {➕} = [≡]-intro
  Commutativity.proof [+]-commutativity {➖} {➖} = [≡]-intro

instance
  [⨯]-commutativity : Commutativity(_⨯_)
  Commutativity.proof [⨯]-commutativity {➕} {➕} = [≡]-intro
  Commutativity.proof [⨯]-commutativity {➕} {➖} = [≡]-intro
  Commutativity.proof [⨯]-commutativity {➖} {➕} = [≡]-intro
  Commutativity.proof [⨯]-commutativity {➖} {➖} = [≡]-intro

instance
  [+₀]-identityₗ : Identityₗ(_+₀_)(𝟎)
  Identityₗ.proof [+₀]-identityₗ {➕} = [≡]-intro
  Identityₗ.proof [+₀]-identityₗ {𝟎} = [≡]-intro
  Identityₗ.proof [+₀]-identityₗ {➖} = [≡]-intro

instance
  [+₀]-identityᵣ : Identityᵣ(_+₀_)(𝟎)
  Identityᵣ.proof [+₀]-identityᵣ {➕} = [≡]-intro
  Identityᵣ.proof [+₀]-identityᵣ {𝟎} = [≡]-intro
  Identityᵣ.proof [+₀]-identityᵣ {➖} = [≡]-intro

instance
  [+₀]-identity : Identity(_+₀_)(𝟎)
  [+₀]-identity = intro

instance
  [+₀]-inverseFunctionₗ : InverseFunctionₗ(_+₀_)(−₀_)
  InverseFunctionₗ.proof [+₀]-inverseFunctionₗ {➕} = [≡]-intro
  InverseFunctionₗ.proof [+₀]-inverseFunctionₗ {𝟎} = [≡]-intro
  InverseFunctionₗ.proof [+₀]-inverseFunctionₗ {➖} = [≡]-intro

instance
  [+₀]-inverseFunctionᵣ : InverseFunctionᵣ(_+₀_)(−₀_)
  InverseFunctionᵣ.proof [+₀]-inverseFunctionᵣ {➕} = [≡]-intro
  InverseFunctionᵣ.proof [+₀]-inverseFunctionᵣ {𝟎} = [≡]-intro
  InverseFunctionᵣ.proof [+₀]-inverseFunctionᵣ {➖} = [≡]-intro

instance
  [+₀]-inverseFunction : InverseFunction(_+₀_)(−₀_)
  [+₀]-inverseFunction = intro

instance
  [⨯₀]-commutativity : Commutativity(_⨯₀_)
  Commutativity.proof [⨯₀]-commutativity {➕} {➕} = [≡]-intro
  Commutativity.proof [⨯₀]-commutativity {➕} {𝟎} = [≡]-intro
  Commutativity.proof [⨯₀]-commutativity {➕} {➖} = [≡]-intro
  Commutativity.proof [⨯₀]-commutativity {𝟎} {➕} = [≡]-intro
  Commutativity.proof [⨯₀]-commutativity {𝟎} {𝟎} = [≡]-intro
  Commutativity.proof [⨯₀]-commutativity {𝟎} {➖} = [≡]-intro
  Commutativity.proof [⨯₀]-commutativity {➖} {➕} = [≡]-intro
  Commutativity.proof [⨯₀]-commutativity {➖} {𝟎} = [≡]-intro
  Commutativity.proof [⨯₀]-commutativity {➖} {➖} = [≡]-intro

instance
  [⨯₀]-associativity : Associativity(_⨯₀_)
  Associativity.proof [⨯₀]-associativity {➕} {➕} {➕} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➕} {➕} {𝟎} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➕} {➕} {➖} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➕} {𝟎} {➕} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➕} {𝟎} {𝟎} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➕} {𝟎} {➖} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➕} {➖} {➕} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➕} {➖} {𝟎} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➕} {➖} {➖} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {𝟎} {➕} {➕} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {𝟎} {➕} {𝟎} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {𝟎} {➕} {➖} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {𝟎} {𝟎} {➕} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {𝟎} {𝟎} {𝟎} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {𝟎} {𝟎} {➖} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {𝟎} {➖} {➕} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {𝟎} {➖} {𝟎} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {𝟎} {➖} {➖} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➖} {➕} {➕} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➖} {➕} {𝟎} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➖} {➕} {➖} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➖} {𝟎} {➕} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➖} {𝟎} {𝟎} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➖} {𝟎} {➖} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➖} {➖} {➕} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➖} {➖} {𝟎} = [≡]-intro
  Associativity.proof [⨯₀]-associativity {➖} {➖} {➖} = [≡]-intro

instance
  [⨯₀]-absorberₗ : Absorberₗ(_⨯₀_)(𝟎)
  Absorberₗ.proof [⨯₀]-absorberₗ {➕} = [≡]-intro
  Absorberₗ.proof [⨯₀]-absorberₗ {𝟎} = [≡]-intro
  Absorberₗ.proof [⨯₀]-absorberₗ {➖} = [≡]-intro

instance
  [⨯₀]-absorberᵣ : Absorberᵣ(_⨯₀_)(𝟎)
  Absorberᵣ.proof [⨯₀]-absorberᵣ {➕} = [≡]-intro
  Absorberᵣ.proof [⨯₀]-absorberᵣ {𝟎} = [≡]-intro
  Absorberᵣ.proof [⨯₀]-absorberᵣ {➖} = [≡]-intro

instance
  [⨯₀]-absorber : Absorber(_⨯₀_)(𝟎)
  [⨯₀]-absorber = intro

instance
  [−]-involution : Involution(−_)
  Involution.proof [−]-involution {➕} = [≡]-intro
  Involution.proof [−]-involution {➖} = [≡]-intro

[−]-no-fixpoints : ∀{s} → (− s ≢ s)
[−]-no-fixpoints {➕} ()
[−]-no-fixpoints {➖} ()
