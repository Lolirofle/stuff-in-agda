open import Type

module Graph.Walk.Functions.Proofs {ℓ₁ ℓ₂} {V : Type{ℓ₁}} where

import      Data.Either as Either
open import Data.Either.Proofs
open import Logic.Propositional
open import Logic.Propositional.Equiv
import      Lvl
open import Graph{ℓ₁}{ℓ₂}(V)
open import Graph.Properties
open import Graph.Walk{ℓ₁}{ℓ₂}{V}
open import Graph.Walk.Properties{ℓ₁}{ℓ₂}{V}
open import Graph.Walk.Functions{ℓ₁}{ℓ₂}{V}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Function
open import Type.Dependent
open import Type.Dependent.Functions

module _ (_⟶_ : Graph) where
  at-path-length : ∀{a} → length{_⟶_}(at{x = a}) ≡ 0
  at-path-length = reflexivity(_≡_)

  edge-path-length : ∀{a b}{e : a ⟶ b} → length{_⟶_}(edge e) ≡ 1
  edge-path-length = reflexivity(_≡_)

  join-path-length : ∀{a b c}{e₁ : a ⟶ b}{e₂ : b ⟶ c} → length{_⟶_}(join e₁ e₂) ≡ 2
  join-path-length = reflexivity(_≡_)

  prepend-path-length : ∀{a b c}{e : a ⟶ b}{w : Walk(_⟶_) b c} → length(prepend e w) ≡ 𝐒(length w)
  prepend-path-length {w = at}          = reflexivity(_≡_)
  prepend-path-length {w = prepend e w} = congruence₁(𝐒) (prepend-path-length{e = e}{w = w})

  [++]-identityᵣ : ∀{a b}{w : Walk(_⟶_) a b} → (w ++ at ≡ w)
  [++]-identityᵣ {w = at}          = reflexivity(_≡_)
  [++]-identityᵣ {w = prepend x w} = congruence₁(prepend x) ([++]-identityᵣ {w = w})
  {-# REWRITE [++]-identityᵣ #-}

  [++]-path-length : ∀{a b c}{w₁ : Walk(_⟶_) a b}{w₂ : Walk(_⟶_) b c} → length(w₁ ++ w₂) ≡ length w₁ + length w₂
  [++]-path-length {a} {.a} {.a} {at}            {at}          = reflexivity(_≡_)
  [++]-path-length {a} {.a} {c}  {at}            {prepend e w} = prepend-path-length {e = e}{w = w}
  [++]-path-length {a} {b}  {c}  {prepend e₁ w₁} {w₂}          = congruence₁(𝐒) ([++]-path-length {w₁ = w₁}{w₂ = w₂})
  {-# REWRITE [++]-path-length #-}

  at-visits : ∀{v} → Visits(_⟶_) v (at{x = v})
  at-visits = current

  edge-visits-left : ∀{a b}{e : a ⟶ b} → Visits(_⟶_) a (edge e)
  edge-visits-left = current

  edge-visits-right : ∀{a b}{e : a ⟶ b} → Visits(_⟶_) b (edge e)
  edge-visits-right = skip current

  join-visits-1 : ∀{a b c}{e₁ : a ⟶ b}{e₂ : b ⟶ c} → Visits(_⟶_) a (join e₁ e₂)
  join-visits-1 = current

  join-visits-2 : ∀{a b c}{e₁ : a ⟶ b}{e₂ : b ⟶ c} → Visits(_⟶_) b (join e₁ e₂)
  join-visits-2 = skip current

  join-visits-3 : ∀{a b c}{e₁ : a ⟶ b}{e₂ : b ⟶ c} → Visits(_⟶_) c (join e₁ e₂)
  join-visits-3 = skip (skip current)

  prepend-visitsᵣ-left : ∀{a b c}{e : a ⟶ b}{w : Walk(_⟶_) b c} → Visits(_⟶_) a (prepend e w)
  prepend-visitsᵣ-left = current

  prepend-visitsᵣ-right : ∀{v b c}{w : Walk(_⟶_) b c} → Visits(_⟶_) v w → ∀{a}{e : a ⟶ b} → Visits(_⟶_) v (prepend e w)
  prepend-visitsᵣ-right p = skip p

  prepend-visitsₗ : ∀{v a b c}{e : a ⟶ b}{w : Walk(_⟶_) b c} → Visits(_⟶_) v (prepend e w) → ((v ≡ a) ∨ Visits(_⟶_) v w)
  prepend-visitsₗ current  = [∨]-introₗ(reflexivity(_≡_))
  prepend-visitsₗ (skip p) = [∨]-introᵣ p

  [++]-visitsᵣ : ∀{v a b c}{w₁ : Walk(_⟶_) a b}{w₂ : Walk(_⟶_) b c} → (Visits(_⟶_) v w₁) ∨ (Visits(_⟶_) v w₂) → Visits(_⟶_) v (w₁ ++ w₂)
  [++]-visitsᵣ ([∨]-introₗ current) = current
  [++]-visitsᵣ {w₂ = w₂} ([∨]-introₗ (skip {rest = rest} p)) = skip ([++]-visitsᵣ {w₁ = rest}{w₂ = w₂} ([∨]-introₗ p))
  [++]-visitsᵣ {w₁ = at} ([∨]-introᵣ p) = p
  [++]-visitsᵣ {w₁ = prepend x w₁} {w₂ = w₂} ([∨]-introᵣ p) = skip ([++]-visitsᵣ {w₁ = w₁}{w₂ = w₂} ([∨]-introᵣ p))

  [++]-visitsₗ : ∀{v a b c}{w₁ : Walk(_⟶_) a b}{w₂ : Walk(_⟶_) b c} → (Visits(_⟶_) v w₁) ∨ (Visits(_⟶_) v w₂) ← Visits(_⟶_) v (w₁ ++ w₂)
  [++]-visitsₗ {v} {a} {.a} {.a} {at}           {at}            p = [∨]-introₗ p
  [++]-visitsₗ {v} {a} {.a} {c}  {at}           {prepend x w₂}  p = [∨]-introᵣ p
  [++]-visitsₗ {v} {a} {b}  {c}  {prepend e w₁} {w₂}            p with prepend-visitsₗ p
  [++]-visitsₗ {v} {a} {b}  {c}  {prepend e w₁} {w₂}            p | [∨]-introₗ eq = [∨]-introₗ (substitute₁ₗ _ eq (Visits.current {path = prepend e w₁}))
  [++]-visitsₗ {v} {a} {b}  {c}  {prepend e w₁} {w₂}            _ | [∨]-introᵣ p  = Either.mapLeft skip ([++]-visitsₗ {w₁ = w₁} {w₂ = w₂} p)
