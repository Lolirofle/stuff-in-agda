module Numeral.Integer.Relation.Divisibility.Proofs where

open import Functional
open import Logic.Propositional
open import Logic.Propositional.Equiv
import      Numeral.Natural.Relation.Divisibility as ℕ
import      Numeral.Natural.Relation.Divisibility.Proofs as ℕ
open import Numeral.Natural using (ℕ)
import      Numeral.Natural.Oper as ℕ
open import Numeral.Integer.Construction
open import Numeral.Integer.Construction.Proofs
open import Numeral.Integer.Function
open import Numeral.Integer.Oper
open import Numeral.Integer.Oper.Proofs
open import Numeral.Integer.Proofs
open import Numeral.Integer.Relation.Divisibility
open import Numeral.Integer
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function.Domain
open import Structure.Function.Multi
open import Structure.Operator.Properties
open import Structure.Relator
open import Structure.Relator.Properties
open import Type

instance
  [∣]-reflexivity : Reflexivity(_∣_)
  [∣]-reflexivity = intro(reflexivity(ℕ._∣_))

-- instance
--   [∣]-antisymmetry : Antisymmetry(_∣_)((_≡_) on₂ abs)
--   Antisymmetry.proof [∣]-antisymmetry x x₁ = {!!}
-- intro(injective(absₙ) ∘₂ antisymmetry(ℕ._∣_)(_≡_))

instance
  [∣]-transitivity : Transitivity(_∣_)
  [∣]-transitivity = intro(transitivity(ℕ._∣_))

instance
  [∣][−𝐒ₙ]-sub : ((_∣_) on₂ (−𝐒ₙ_)) ⊆₂ ((ℕ._∣_) on₂ ℕ.𝐒)
  [∣][−𝐒ₙ]-sub = intro id

instance
  [∣][+ₙ]-sub : ((_∣_) on₂ (+ₙ_)) ⊆₂ (ℕ._∣_)
  [∣][+ₙ]-sub = intro id

instance
  [∣][−ₙ]-sub : ((_∣_) on₂ (−ₙ_)) ⊆₂ (ℕ._∣_)
  _⊆₂_.proof [∣][−ₙ]-sub {ℕ.𝟎}   {ℕ.𝟎}   p = p
  _⊆₂_.proof [∣][−ₙ]-sub {ℕ.𝟎}   {ℕ.𝐒 y} p = p
  _⊆₂_.proof [∣][−ₙ]-sub {ℕ.𝐒 x} {ℕ.𝟎}   p = p
  _⊆₂_.proof [∣][−ₙ]-sub {ℕ.𝐒 x} {ℕ.𝐒 y} p = p

instance
  [∣][−𝐒ₙ]-super : ((_∣_) on₂ (−𝐒ₙ_)) ⊇₂ ((ℕ._∣_) on₂ ℕ.𝐒)
  [∣][−𝐒ₙ]-super = intro id

instance
  [∣][+ₙ]-super : ((_∣_) on₂ (+ₙ_)) ⊇₂ (ℕ._∣_)
  [∣][+ₙ]-super = intro id

instance
  [∣][−ₙ]-super : ((_∣_) on₂ (−ₙ_)) ⊇₂ (ℕ._∣_)
  _⊆₂_.proof [∣][−ₙ]-super {ℕ.𝟎}   {ℕ.𝟎}   p = p
  _⊆₂_.proof [∣][−ₙ]-super {ℕ.𝟎}   {ℕ.𝐒 y} p = p
  _⊆₂_.proof [∣][−ₙ]-super {ℕ.𝐒 x} {ℕ.𝟎}   p = p
  _⊆₂_.proof [∣][−ₙ]-super {ℕ.𝐒 x} {ℕ.𝐒 y} p = p

divides-with-[−ₙ] : ∀{a b c} → ((absₙ a) ℕ.∣ b) → ((absₙ a) ℕ.∣ c) → (a ∣ (b −ₙ c))
divides-with-[−ₙ] {a} ℕ.Div𝟎 ℕ.Div𝟎 = ℕ.Div𝟎
divides-with-[−ₙ] {a} (ℕ.Div𝐒 ab) ℕ.Div𝟎 = ℕ.Div𝐒 ab
divides-with-[−ₙ] {a} ℕ.Div𝟎 (ℕ.Div𝐒 {x = x} ac)
  with p ← ℕ.divides-with-[+] (reflexivity(ℕ._∣_)) ((super₂((_∣_) on₂ (−ₙ_))(ℕ._∣_) ac))
  rewrite absₙ-of-[−ₙ] {x}
  rewrite absₙ-of-[−ₙ] {absₙ a}
  rewrite [−ₙ]-antiidentityₗ {absₙ a ℕ.+ x}
  rewrite absₙ-of-[−ₙ] {absₙ(a) ℕ.+ x}
  = p
divides-with-[−ₙ] {a} (ℕ.Div𝐒 {x = x} ab) (ℕ.Div𝐒 {x = y} ac)
  rewrite [−ₙ]-on-[+]ₗ-redundancy{absₙ a}{x}{y}
  = divides-with-[−ₙ] {a} ab ac

divides-with-[+] : ∀{a b c} → (a ∣ b) → (a ∣ c) → (a ∣ (b + c))
divides-with-[+] {+ₙ  a} {+ₙ  b} {+ₙ  c} ab ac = ℕ.divides-with-[+] ab ac
divides-with-[+] {+ₙ  a} {+ₙ  b} {−𝐒ₙ c} ab ac = divides-with-[−ₙ] {+ₙ a} ab ac
divides-with-[+] {+ₙ  a} {−𝐒ₙ b} {+ₙ  c} ab ac = divides-with-[−ₙ] {+ₙ a} ac ab
divides-with-[+] {+ₙ  a} {−𝐒ₙ b} {−𝐒ₙ c} ab ac = ℕ.divides-with-[+] ab ac
divides-with-[+] {−𝐒ₙ a} {+ₙ  b} {+ₙ  c} ab ac = ℕ.divides-with-[+] ab ac
divides-with-[+] {−𝐒ₙ a} {+ₙ  b} {−𝐒ₙ c} ab ac = divides-with-[−ₙ] {−𝐒ₙ a} ab ac
divides-with-[+] {−𝐒ₙ a} {−𝐒ₙ b} {+ₙ  c} ab ac = divides-with-[−ₙ] {−𝐒ₙ a} ac ab
divides-with-[+] {−𝐒ₙ a} {−𝐒ₙ b} {−𝐒ₙ c} ab ac = ℕ.divides-with-[+] ab ac

divides-with-[⋅] : ∀{a b c} → ((a ∣ b) ∨ (a ∣ c)) → (a ∣ (b ⋅ c))
divides-with-[⋅] {a} {b} {c} p = substitute₂-₂ₗ(ℕ._∣_)(absₙ a)
  (preserving₂(absₙ)(_⋅_)(ℕ._⋅_) {b}{c})
  (ℕ.divides-with-[⋅] {absₙ a}{absₙ b}{absₙ c} p)

divides-[⋅]ₗ : ∀{a b} → (a ∣ (a ⋅ b))
divides-[⋅]ₗ {a}{b} = divides-with-[⋅] {a}{a}{b} ([∨]-introₗ (reflexivity(_∣_) {a}))

divides-[⋅]ᵣ : ∀{a b} → (b ∣ (a ⋅ b))
divides-[⋅]ᵣ {a}{b} = divides-with-[⋅] {b}{a}{b} ([∨]-introᵣ (reflexivity(_∣_) {b}))

divides-with-[−] : ∀{a b c} → (a ∣ b) → (a ∣ c) → (a ∣ (b − c))
divides-with-[−] {a}{b}{c} ab ac = divides-with-[+] {a}{b}{− c} ab (substitute₂-₂ₗ(ℕ._∣_)(absₙ a) (absₙ-of-[−] {c}) ac)

divides-with-[⋅]-both : ∀{a₁ a₂ b₁ b₂} → (a₁ ∣ b₁) → (a₂ ∣ b₂) → ((a₁ ⋅ a₂) ∣ (b₁ ⋅ b₂))
divides-with-[⋅]-both {a₁} {a₂} {b₁} {b₂} ab₁ ab₂ = substitute₂ₗ(ℕ._∣_)
  (preserving₂(absₙ)(_⋅_)(ℕ._⋅_) {a₁}{a₂})
  (preserving₂(absₙ)(_⋅_)(ℕ._⋅_) {b₁}{b₂})
  (ℕ.divides-with-[⋅]-both ab₁ ab₂)
