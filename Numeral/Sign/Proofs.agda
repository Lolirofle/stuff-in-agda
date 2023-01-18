module Numeral.Sign.Proofs where

open import Logic.IntroInstances
open import Numeral.Charge.Proofs using (Charge-equiv)
open import Numeral.Sign
open import Numeral.Sign.Oper
open import Relator.Equals
open import Relator.Equals.Proofs.Equivalence
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Setoid hiding (_≡_ ; _≢_)
open import Type

instance
  Sign-equiv : Equiv(Sign)
  Sign-equiv = [≡]-equiv

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
  [⨯]-identityₗ : Identityₗ(_⨯_)(➕)
  Identityₗ.proof [⨯]-identityₗ {➕} = [≡]-intro
  Identityₗ.proof [⨯]-identityₗ {➖} = [≡]-intro

instance
  [⨯]-identityᵣ : Identityᵣ(_⨯_)(➕)
  Identityᵣ.proof [⨯]-identityᵣ {➕} = [≡]-intro
  Identityᵣ.proof [⨯]-identityᵣ {➖} = [≡]-intro

instance
  [⨯]-identity : Identity(_⨯_)(➕)
  [⨯]-identity = intro

instance
  [−]-involution : Involution(−_)
  Involution.proof [−]-involution {➕} = [≡]-intro
  Involution.proof [−]-involution {➖} = [≡]-intro

[−]-no-fixpoints : ∀{s} → (− s ≢ s)
[−]-no-fixpoints {➕} ()
[−]-no-fixpoints {➖} ()
