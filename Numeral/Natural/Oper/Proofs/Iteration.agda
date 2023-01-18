module Numeral.Natural.Oper.Proofs.Iteration where

open import Functional
open import Function.Iteration using (repeatᵣ ; repeatₗ) renaming (_^_ to _^ᶠ_)
open import Function.Iteration.Proofs
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Properties
open import Syntax.Transitivity

[^]-of-𝐒-𝟎-identity : ∀{x} → ((𝐒 ^ᶠ x) 𝟎 ≡ x)
[^]-of-𝐒-𝟎-identity {𝟎}   = [≡]-intro
[^]-of-𝐒-𝟎-identity {𝐒 x} = congruence₁(𝐒) ([^]-of-𝐒-𝟎-identity {x})

-- Addition as iterated successors.
[+]-iterateₗ-𝐒 : ∀{x y} → (x + y ≡ (𝐒 ^ᶠ x)(y))
[+]-iterateₗ-𝐒 {x}{𝟎}   = symmetry(_≡_) ([^]-of-𝐒-𝟎-identity {x})
[+]-iterateₗ-𝐒 {x}{𝐒 y} =
  x + 𝐒(y)       🝖[ _≡_ ]-[]
  𝐒(x + y)       🝖[ _≡_ ]-[ congruence₁(𝐒) ([+]-iterateₗ-𝐒 {x}{y}) ]
  𝐒((𝐒 ^ᶠ x)(y)) 🝖[ _≡_ ]-[]
  (𝐒 ^ᶠ 𝐒(x))(y) 🝖[ _≡_ ]-[ [^]-inner-value {f = 𝐒}{y}{x} ]-sym
  (𝐒 ^ᶠ x)(𝐒(y)) 🝖-end

-- Addition as iterated successors.
[+]-iterateᵣ-𝐒 : ∀{x y} → (x + y ≡ (𝐒 ^ᶠ y)(x))
[+]-iterateᵣ-𝐒 {x} {𝟎}   = [≡]-intro
[+]-iterateᵣ-𝐒 {x} {𝐒 y} = congruence₁(𝐒) ([+]-iterateᵣ-𝐒 {x}{y})

-- Addition as repeated successors.
[+]-repeatᵣ-𝐒 : ∀{x y z : ℕ} → (x + y ≡ repeatᵣ y (const 𝐒) z x)
[+]-repeatᵣ-𝐒 {x}{y} = [+]-iterateᵣ-𝐒 {x}{y}

-- Multiplication as repeated additions.
[⋅]-repeatᵣ-[+] : ∀{x y} → (x ⋅ y ≡ repeatᵣ y (_+_) x 0)
[⋅]-repeatᵣ-[+] {x} {𝟎}   = [≡]-intro
[⋅]-repeatᵣ-[+] {x} {𝐒 y} = congruence₁(x +_) ([⋅]-repeatᵣ-[+] {x} {y})

-- Exponentiation as repeated multiplications.
[^]-repeatᵣ-[⋅] : ∀{x y} → (x ^ y ≡ repeatᵣ y (_⋅_) x 1)
[^]-repeatᵣ-[⋅] {x} {𝟎}   = [≡]-intro
[^]-repeatᵣ-[⋅] {x} {𝐒 y} = congruence₁(x ⋅_) ([^]-repeatᵣ-[⋅] {x} {y})

[⋅]-stepₗ-iterateᵣ-𝐒 : ∀{x y} → (𝐒(x) ⋅ y ≡ (𝐒 ^ᶠ y)(x ⋅ y))
[⋅]-stepₗ-iterateᵣ-𝐒 {x}{y} =
  𝐒(x) ⋅ y        🝖[ _≡_ ]-[ [⋅]-with-[𝐒]ₗ {x}{y} ]
  (x ⋅ y) + y     🝖[ _≡_ ]-[ [+]-iterateᵣ-𝐒 {x ⋅ y}{y} ]
  (𝐒 ^ᶠ y)(x ⋅ y) 🝖-end

[⋅]-stepᵣ-iterateₗ-𝐒 : ∀{x y} → (x ⋅ 𝐒(y) ≡ (𝐒 ^ᶠ x)(x ⋅ y))
[⋅]-stepᵣ-iterateₗ-𝐒 {x}{y} =
  x ⋅ 𝐒(y)        🝖[ _≡_ ]-[]
  x + (x ⋅ y)     🝖[ _≡_ ]-[ [+]-iterateₗ-𝐒 {x}{x ⋅ y} ]
  (𝐒 ^ᶠ x)(x ⋅ y) 🝖-end
