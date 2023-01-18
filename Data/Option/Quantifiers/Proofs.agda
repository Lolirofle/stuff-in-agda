module Data.Option.Quantifiers.Proofs where

import      Lvl
open import Data
open import Data.Option
import      Data.Option.Functions as Option
open import Data.Option.Quantifiers
open import Functional
open import Logic.Propositional
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable f : A → B
private variable P Q : T → Type{ℓ}
private variable o : Option(T)

[∀ₒₚₜ]-of-map : ∀ₒₚₜ(Option.map f o) P ↔ ∀ₒₚₜ(o) (P ∘ f)
[∀ₒₚₜ]-of-map {o = None}   = [↔]-intro id id
[∀ₒₚₜ]-of-map {o = Some _} = [↔]-intro id id

[∀ₒₚₜ]-map : (∀{x} → P(x) → Q(x)) → (∀ₒₚₜ(o) P → ∀ₒₚₜ(o) Q)
[∀ₒₚₜ]-map {o = None}   pq <> = <>
[∀ₒₚₜ]-map {o = Some _} pq p  = pq p

[∃ₒₚₜ]-of-map : ∃ₒₚₜ(Option.map f o) P ↔ ∃ₒₚₜ(o) (P ∘ f)
[∃ₒₚₜ]-of-map {o = None}   = [↔]-intro id id
[∃ₒₚₜ]-of-map {o = Some _} = [↔]-intro id id

[∃ₒₚₜ]-map : (∀{x} → P(x) → Q(x)) → (∃ₒₚₜ(o) P → ∃ₒₚₜ(o) Q)
[∃ₒₚₜ]-map {o = None}   pq ()
[∃ₒₚₜ]-map {o = Some _} pq p  = pq p

[∃ₒₚₜ]-of-⊥ : ∃ₒₚₜ(o) (const ⊥) → ⊥
[∃ₒₚₜ]-of-⊥ {o = None}   ()
[∃ₒₚₜ]-of-⊥ {o = Some _} ()
