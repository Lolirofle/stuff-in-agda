module Numeral.Finite.Oper.Exact.Proofs where

open import Data
open import Numeral.Natural
open import Numeral.Finite
import      Numeral.Finite.Oper
open        Numeral.Finite.Oper.Exact
open import Numeral.Finite.Relation.Order
open import Numeral.Finite.Relation.Order.Proofs
open import Structure.Function
open import Type.Identity
open import Type.Identity.Proofs

private instance _ = Id-to-function
private variable b₁ b₂ N : ℕ
private variable n x y z x₁ x₂ y₁ y₂ : 𝕟(N)

𝐒-function : (x ≡ y) → (𝐒(x) ≡ 𝐒(y))
𝐒-function xy = xy

[+₌]-stepₗ : (𝐒(x) +₌ y) ≡ (𝐒(x +₌ y))
[+₌]-stepₗ {b₁}  {𝟎}  {b₂}  {𝟎}   = <>
[+₌]-stepₗ {b₁}  {𝟎}  {𝐒 b₂}{𝐒 y} = [+₌]-stepₗ {b₁}{𝟎}{b₂}{y}
[+₌]-stepₗ {𝐒 b₁}{𝐒 x}{b₂}  {y}   = [+₌]-stepₗ {b₁}{x}{b₂}{y}

[+₌]-stepᵣ : (x +₌ 𝐒(y)) ≡ (𝐒(x +₌ y))
[+₌]-stepᵣ {b₁}  {𝟎}  {b₂}  {𝟎}   = <>
[+₌]-stepᵣ {b₁}  {𝟎}  {𝐒 b₂}{𝐒 y} = [+₌]-stepᵣ {b₁}{𝟎}{b₂}{y}
[+₌]-stepᵣ {𝐒 b₁}{𝐒 x}{b₂}  {y}   = [+₌]-stepᵣ {b₁}{x}{b₂}{y}

[+₌]-identityₗ : (_+₌_ {b₁}{b₂} 𝟎 y) ≡ y
[+₌]-identityₗ {b₁}{b₂}  {𝟎}   = <>
[+₌]-identityₗ {b₁}{𝐒 b₂}{𝐒 y} = [+₌]-identityₗ {b₁}{b₂}{y}

[+₌]-identityᵣ : (_+₌_ {b₁}{b₂} x 𝟎) ≡ x
[+₌]-identityᵣ {b₁}  {b₂}{𝟎}   = <>
[+₌]-identityᵣ {𝐒 b₁}{b₂}{𝐒 x} = [+₌]-identityᵣ {b₁}{b₂}{x}

open import Numeral.Finite.Equiv2
open import Syntax.Transitivity.Structure
open import Type.Dependent.Sigma.Implicit renaming (intro to •_)

[+₌]-function : (x₁ ≡ x₂) → (y₁ ≡ y₂) → ((x₁ +₌ y₁) ≡ (x₂ +₌ y₂))
[+₌]-function {x₁ = x₁} {x₂ = x₂} {y₁ = 𝟎} {y₂ = 𝟎} px py = 🝖-begin
  • (x₁ +₌ 𝟎) 🝖[ _≡*_ ]-[ [+₌]-identityᵣ {x = x₁} ]
  • x₁        🝖[ _≡*_ ]-[ px ]
  • x₂        🝖[ _≡*_ ]-[ [+₌]-identityᵣ {x = x₂} ]-sym
  • (x₂ +₌ 𝟎) 🝖-end
[+₌]-function {x₁ = x₁} {x₂ = x₂} {𝐒 _} {y₁ = 𝐒 y₁} {𝐒 _} {y₂ = 𝐒 y₂} px py = 🝖-begin
  • (x₁ +₌ 𝐒(y₁)) 🝖[ _≡*_ ]-[ [+₌]-stepᵣ {x = x₁}{y = y₁} ]
  • 𝐒(x₁ +₌ y₁)   🝖[ _≡*_ ]-[ [+₌]-function {x₁ = x₁}{x₂ = x₂}{y₁ = y₁}{y₂ = y₂} px py ]
  • 𝐒(x₂ +₌ y₂)   🝖[ _≡*_ ]-[ [+₌]-stepᵣ {x = x₂}{y = y₂} ]-sym
  • (x₂ +₌ 𝐒(y₂)) 🝖-end

[+₌]-associativity : ((x +₌ y) +₌ z) ≡ (x +₌ (y +₌ z))
[+₌]-associativity {b₁} {x} {b₂} {y} {b₃} {𝟎} = 🝖-begin
  (• ((x +₌ y) +₌ 𝟎)) 🝖[ _≡*_ ]-[ [+₌]-identityᵣ {x = x +₌ y} ]
  (• (x +₌ y))        🝖[ _≡*_ ]-[ [+₌]-function {x₁ = x}{x₂ = x} ([≡]-reflexivity-raw {a = x}) ([+₌]-identityᵣ {x = y}) ]-sym
  (• (x +₌ (y +₌ 𝟎))) 🝖-end
[+₌]-associativity {b₁} {x} {b₂} {y} {𝐒 _} {𝐒 z} = 🝖-begin
  (• ((x +₌ y) +₌ 𝐒(z))) 🝖[ _≡*_ ]-[ [+₌]-stepᵣ {x = x +₌ y}{y = z} ]
  (• 𝐒((x +₌ y) +₌ z))   🝖[ _≡*_ ]-[ [+₌]-associativity {x = x}{y = y}{z = z} ]
  (• 𝐒(x +₌ (y +₌ z)))   🝖[ _≡*_ ]-[ [+₌]-stepᵣ {x = x}{y = y +₌ z} ]-sym
  (• (x +₌ 𝐒(y +₌ z)))   🝖[ _≡*_ ]-[ [+₌]-function {x₁ = x}{x₂ = x} ([≡]-reflexivity-raw {a = x}) ([+₌]-stepᵣ {x = y}{y = z}) ]-sym
  (• (x +₌ (y +₌ 𝐒(z)))) 🝖-end

[+₌]-commutativity : (x +₌ y) ≡ (y +₌ x)
[+₌]-commutativity {b₁} {x} {b₂} {𝟎} = 🝖-begin
  • (x +₌ 𝟎) 🝖[ _≡*_ ]-[ [+₌]-identityᵣ {x = x} ]
  • x        🝖[ _≡*_ ]-[ [+₌]-identityₗ {y = x} ]-sym
  • (𝟎 +₌ x) 🝖-end
[+₌]-commutativity {b₁} {x} {𝐒 b₂} {𝐒 y} = 🝖-begin
  • (x +₌ 𝐒(y)) 🝖[ _≡*_ ]-[ [+₌]-stepᵣ {x = x}{y = y} ]
  • 𝐒(x +₌ y)   🝖[ _≡*_ ]-[ [+₌]-commutativity {x = x}{y = y} ]
  • 𝐒(y +₌ x)   🝖[ _≡*_ ]-[ [+₌]-stepₗ {x = y}{y = x} ]-sym
  • (𝐒(y) +₌ x) 🝖-end

{-
open import Numeral.Finite.Bound

[+₌]-bound-stepₗ : Id(bound-𝐒(x) +₌ y) (bound-𝐒(x +₌ y))
[+₌]-bound-stepₗ {b₁} {𝟎} {b₂} {𝟎} = intro
[+₌]-bound-stepₗ {b₁} {𝟎} {b₂} {𝐒 y} = {!!}
[+₌]-bound-stepₗ {b₁} {𝐒 x} {b₂} {𝟎} = {!!}
[+₌]-bound-stepₗ {b₁} {𝐒 x} {b₂} {𝐒 y} = {!!}
-}
