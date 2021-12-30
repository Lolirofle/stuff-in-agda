module Numeral.Finite.Oper.Proofs where

open import Data
open import Data.Boolean
open import Functional
open import Logic.Predicate
open import Numeral.Finite
open import Numeral.Finite.Oper
open import Numeral.Finite.Proofs
import      Numeral.Finite.Relation.Order as 𝕟
open import Numeral.Natural
import      Numeral.Natural.Relation as ℕ
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
import      Structure.Function.Names as Names
open import Structure.Relator.Properties
open import Syntax.Transitivity

bounded-𝐏-𝐒-inverses : ∀{n} ⦃ pos : ℕ.Positive(n) ⦄ {x : 𝕟(n)} → (Bounded.𝐏(𝐒(x)) ≡ x)
bounded-𝐏-𝐒-inverses {𝐒 𝟎}   {x = 𝟎}   = [≡]-intro
bounded-𝐏-𝐒-inverses {𝐒(𝐒 n)}{x = 𝟎}   = [≡]-intro
bounded-𝐏-𝐒-inverses {𝐒(𝐒 n)}{x = 𝐒 x} = congruence₁(𝐒) (bounded-𝐏-𝐒-inverses{𝐒 n}{x = x})

𝐒-bounded-𝐏-inverses : ∀{n} ⦃ pos-n : ℕ.Positive(n) ⦄ {x : 𝕟(𝐒 n)} → ⦃ pos-x : 𝕟.Positive(x) ⦄ → (𝐒(Bounded.𝐏(x)) ≡ x)
𝐒-bounded-𝐏-inverses {𝐒 𝟎}    {x = 𝐒 𝟎}    = [≡]-intro
𝐒-bounded-𝐏-inverses {𝐒 (𝐒 n)}{x = 𝐒 𝟎}    = [≡]-intro
𝐒-bounded-𝐏-inverses {𝐒 (𝐒 n)}{x = 𝐒(𝐒 x)} = congruence₁(𝐒) (𝐒-bounded-𝐏-inverses {𝐒 n}{x = 𝐒 x})

shiftRepeat-def1 : ∀{n} ⦃ pos : ℕ.Positive(n) ⦄ {c : 𝕟(n)}{x : 𝕟(𝐒(n))} → (c 𝕟.< x) → (shiftRepeat c x ≡ Bounded.𝐏(x))
shiftRepeat-def1 {.(𝐒 _)}     {c = 𝟎}         {𝐒 x}        cx = symmetry(_≡_) bounded-𝐏-𝐒-inverses
shiftRepeat-def1 {.(𝐒 (𝐒 n))} {c = 𝐒 {𝐒 n} c} {𝐒(x@(𝐒 _))} cx =
  shiftRepeat(𝐒(c)) (𝐒(x)) 🝖[ _≡_ ]-[ congruence₁(𝐒) (shiftRepeat-def1 {c = c} {x} cx) ]
  𝐒(Bounded.𝐏(x))          🝖[ _≡_ ]-[ 𝐒-bounded-𝐏-inverses ]
  x                        🝖[ _≡_ ]-[ bounded-𝐏-𝐒-inverses ]-sym
  Bounded.𝐏(𝐒(x))          🝖-end
shiftRepeat-def1 {.(𝐒 (𝐒 n))} {c = 𝐒 {𝐒 n} 𝟎} {𝐒 𝟎} ()
shiftRepeat-def1 {.(𝐒 (𝐒 n))} {c = 𝐒 {𝐒 n} (𝐒 c)} {𝐒 𝟎} ()

shiftRepeat-def2 : ∀{n}{c : 𝕟(n)}{x : 𝕟(𝐒(n))} → (c 𝕟.≥ x) → (shiftRepeat c x 𝕟.≡ x)
shiftRepeat-def2 {𝐒 n} {c = 𝟎} {𝟎} cx = <>
shiftRepeat-def2 {𝐒 n} {c = 𝐒 c} {𝟎} cx = <>
shiftRepeat-def2 {𝐒 (𝐒 n)} {c = 𝐒 c} {𝐒 x} cx = shiftRepeat-def2 {𝐒 n} {c = c} {x} cx

shiftRepeat-surjective : ∀{n}{c : 𝕟(n)} → Surjective(shiftRepeat c)
shiftRepeat-surjective = intro p where
  p : ∀{n}{c : 𝕟(n)} → Names.Surjective(shiftRepeat c)
  p{𝐒 n}{c}  {𝟎}   = [∃]-intro 𝟎
  p{𝐒 n}{𝟎}  {𝐒 y} = [∃]-intro (𝐒(𝐒(y)))
  p{𝐒 n}{𝐒 c}{𝐒 y} =
    let [∃]-intro prev ⦃ eq ⦄ = p{n}{c}{y}
    in [∃]-intro (𝐒(prev)) ⦃ congruence₁(𝐒) eq ⦄

shiftSkip-injective : ∀{n}{c : 𝕟(𝐒(n))}{x y} .⦃ cx : c 𝕟.≢ x ⦄ .⦃ cy : c 𝕟.≢ y ⦄ → (shiftSkip c x ≡ shiftSkip c y) → (x ≡ y)
shiftSkip-injective {𝐒 n} {𝟎}   {𝐒 x} {𝐒 y} = congruence₁(𝐒)
shiftSkip-injective {𝐒 n} {𝐒 c} {𝟎}   {𝟎}   = const [≡]-intro
shiftSkip-injective {𝐒 n} {𝐒 c} {𝐒 x} {𝐒 y} = congruence₁(𝐒) ∘ shiftSkip-injective {n} {c} {x} {y} ∘ injective(𝐒)

shiftRepeat'-almost-injective : ∀{n} ⦃ pos : ℕ.Positive(n) ⦄ {c : 𝕟(𝐒(n))}{x y} .⦃ cx : c 𝕟.≢ x ⦄ .⦃ cy : c 𝕟.≢ y ⦄ → (shiftRepeat' c x ≡ shiftRepeat' c y) → (x ≡ y)
shiftRepeat'-almost-injective {𝐒 𝟎}   {𝟎}  {𝐒 𝟎}{𝐒 𝟎} _ = [≡]-intro
shiftRepeat'-almost-injective {𝐒 𝟎}   {𝐒 c}{𝟎}  {𝟎}   _ = [≡]-intro
shiftRepeat'-almost-injective {𝐒 𝟎}   {𝐒 𝟎}{𝟎}  {𝐒 𝟎} ⦃ _ ⦄ ⦃  ⦄
shiftRepeat'-almost-injective {𝐒 𝟎}   {𝐒 c}{𝐒 𝟎}{𝐒 𝟎} _ = [≡]-intro
shiftRepeat'-almost-injective {𝐒 𝟎}   {𝐒 𝟎}{𝐒 𝟎}{𝟎}   ⦃ ⦄   ⦃ _ ⦄
shiftRepeat'-almost-injective {𝐒(𝐒 n)}{𝐒 c}{𝟎}  {𝟎}     = const [≡]-intro
shiftRepeat'-almost-injective {𝐒(𝐒 n)}{𝟎}  {𝐒 x}{𝐒 y}   = congruence₁(𝐒)
shiftRepeat'-almost-injective {𝐒(𝐒 n)}{𝐒 c}{𝐒 x}{𝐒 y}   = congruence₁(𝐒) ∘ shiftRepeat'-almost-injective {𝐒 n}{c}{x}{y} ∘ injective(𝐒)

shiftRepeat-shiftSkip-eq : ∀{n}{c₁ c₂}{x : 𝕟(𝐒(n))} ⦃ nc₂x : c₂ 𝕟.≢ x ⦄ → (c₁ 𝕟.≡ c₂) → (shiftRepeat c₁ x ≡ shiftSkip c₂ x)
shiftRepeat-shiftSkip-eq {c₁ = 𝟎}   {𝟎}   {𝐒 x} c₁c₂ = [≡]-intro
shiftRepeat-shiftSkip-eq {c₁ = 𝐒 c₁}{𝐒 c₂}{𝟎}   c₁c₂ = [≡]-intro
shiftRepeat-shiftSkip-eq {c₁ = 𝐒 c₁}{𝐒 c₂}{𝐒 x} c₁c₂ = congruence₁(𝐒) (shiftRepeat-shiftSkip-eq {c₁ = c₁}{c₂}{x} c₁c₂)

shiftRepeat-shiftRepeat'-eq : ∀{n} ⦃ pos : ℕ.Positive(n) ⦄ {c₁ c₂}{x : 𝕟(𝐒(n))} → (c₁ 𝕟.≡ c₂) → (shiftRepeat c₁ x ≡ shiftRepeat' c₂ x)
shiftRepeat-shiftRepeat'-eq {𝐒 𝟎}   {𝟎}    {𝟎}   {𝟎}   c₁c₂ = [≡]-intro
shiftRepeat-shiftRepeat'-eq {𝐒 𝟎}   {𝟎}    {𝟎}   {𝐒 𝟎} c₁c₂ = [≡]-intro
shiftRepeat-shiftRepeat'-eq {𝐒(𝐒 n)}{𝟎}    {𝟎}   {𝟎}   c₁c₂ = [≡]-intro
shiftRepeat-shiftRepeat'-eq {𝐒(𝐒 n)}{𝟎}    {𝟎}   {𝐒 x} c₁c₂ = [≡]-intro
shiftRepeat-shiftRepeat'-eq {𝐒(𝐒 n)}{𝐒 c₁} {𝐒 c₂}{𝟎}   c₁c₂ = [≡]-intro
shiftRepeat-shiftRepeat'-eq {𝐒(𝐒 n)}{𝐒 c₁} {𝐒 c₂}{𝐒 x} c₁c₂ = congruence₁(𝐒) (shiftRepeat-shiftRepeat'-eq {𝐒 n}{c₁}{c₂}{x} c₁c₂)
