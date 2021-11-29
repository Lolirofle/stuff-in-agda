module Data.List.FunctionsProven.Proofs where

import      Lvl
open import Data.List
import      Data.List.Functions as List
open import Data.List.FunctionsProven
open import Data.List.Relation.Quantification
import      Functional as Fn
open import Functional.Dependent
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Operator
open import Type
open import Type.Dependent

private variable ℓ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable l l₁ l₂ : List(T)
private variable ll : List(List(T))
private variable x y : T
private variable P Q : T → Type{ℓ}
private variable ap aq : AllElements P(l)
private variable f g : A → B

map-preserves-id : (map constAlt l ap ≡ l)
map-preserves-id {l = ∅}     {ap = ∅}      = [≡]-intro
map-preserves-id {l = x ⊰ l} {ap = p ⊰ ap} = congruence₂ᵣ(_⊰_)(x) (map-preserves-id {l = l}{ap = ap})

map-preserves-[∘] : let _ = A ; _ = B ; _ = C ; _ = P ; _ = Q in ∀{f : (b : B) → P(b) → C}{g : (a : A) → Q(a) → B}{aq : AllElements Q(l)}{ap : AllElements P(map g l aq)} → (qp : ∀{a} → (qa : Q(a)) → P(g a qa)) → (∀{x}{p q} → (f x p ≡ f x q)) → (map f (map g l aq) ap ≡ map (\a qa → f(g a qa) (qp qa)) l aq)
map-preserves-[∘] {l = ∅}     {aq = ∅}      {ap = ∅}      qp fpq = [≡]-intro
map-preserves-[∘] {l = x ⊰ l} {aq = q ⊰ aq} {ap = p ⊰ ap} qp fpq = congruence₂(_⊰_) fpq (map-preserves-[∘] {l = l}{aq = aq}{ap = ap} qp fpq)

-- map-is-map : (map (constAlt ∘ f) l ap ≡ List.map f l)
map-is-map : (map (Fn.const ∘ f) l ap ≡ List.map f l)
map-is-map {l = ∅}     {ap = ∅}      = [≡]-intro
map-is-map {l = x ⊰ l} {ap = p ⊰ ap} = congruence₂(_⊰_) [≡]-intro (map-is-map {l = l}{ap = ap})

-- map-is-Σ-map : (map ? l ap ≡ List.map f l)
