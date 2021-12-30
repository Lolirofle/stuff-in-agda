module Numeral.Natural.Coprime.Tree where

import      Lvl
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Syntax.Transitivity
open import Type

private variable n a b : ℕ

-- An alternative inductive definition of two numbers being coprime (excluding symmetry).
data CoprimeTree : (a : ℕ) → (b : ℕ) → Type{Lvl.𝟎} where
  leaf₁ : CoprimeTree 1 2
  leaf₂ : CoprimeTree 1 3
  branch₁ : (CoprimeTree a b) → (CoprimeTree b ((2 ⋅ b) −₀ a))
  branch₂ : (CoprimeTree a b) → (CoprimeTree b ((2 ⋅ b) + a))
  branch₃ : (CoprimeTree a b) → (CoprimeTree a ((2 ⋅ a) + b))

open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Numeral.Natural.Coprime
open import Numeral.Natural.Coprime.Proofs
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Implication

CoprimeTree-order : (CoprimeTree a b) → (a < b)
CoprimeTree-order leaf₁ = succ (succ min)
CoprimeTree-order leaf₂ = succ (succ min)
CoprimeTree-order {b}{_} (branch₁{c}{_} t) =
  𝐒(b)         🝖[ _≤_ ]-[]
  b + 1        🝖[ _≤_ ]-[ [≤]-with-[+] {b}{b} ⦃ reflexivity(_≤_) ⦄ {1}{b −₀ c} ⦃ [<][−₀]-transfer (CoprimeTree-order t) ⦄ ]
  b + (b −₀ c) 🝖[ _≡_ ]-[ symmetry(_≡_) ([+][−₀]-almost-associativity {b}{b}{c} ([≤]-predecessor (CoprimeTree-order t))) ]-sub
  (b + b) −₀ c 🝖[ _≡_ ]-[ congruence₂-₁(_−₀_)(c) (commutativity(_⋅_) {b}{2}) ]-sub
  (2 ⋅ b) −₀ c 🝖-end
CoprimeTree-order {b}{_} (branch₂{c}{_} t) =
  𝐒(b)        🝖[ _≤_ ]-[]
  b + 1       🝖[ _≤_ ]-[ [≤]-with-[+] {b}{b} ⦃ reflexivity(_≤_) ⦄ {1}{b + c} ⦃ succ min 🝖 CoprimeTree-order t 🝖 [≤]-of-[+]ₗ {b}{c} ⦄ ]
  b + (b + c) 🝖[ _≡_ ]-[ symmetry(_≡_) (associativity(_+_) {b}{b}{c}) ]-sub
  (b + b) + c 🝖[ _≡_ ]-[ congruence₂-₁(_+_)(c) (commutativity(_⋅_) {b}{2}) ]-sub
  (2 ⋅ b) + c 🝖-end
CoprimeTree-order {b}{_} (branch₃{_}{c} t) =
  𝐒(b)        🝖[ _≤_ ]-[]
  b + 1       🝖[ _≤_ ]-[ [≤]-with-[+] {b}{b} ⦃ reflexivity(_≤_) ⦄ {1}{b + c} ⦃ succ min 🝖 CoprimeTree-order t 🝖 [≤]-of-[+]ᵣ {b}{c} ⦄ ]
  b + (b + c) 🝖[ _≡_ ]-[ symmetry(_≡_) (associativity(_+_) {b}{b}{c}) ]-sub
  (b + b) + c 🝖[ _≡_ ]-[ congruence₂-₁(_+_)(c) (commutativity(_⋅_) {b}{2}) ]-sub
  (2 ⋅ b) + c 🝖-end

CoprimeTreeₗ-lower-bound : (CoprimeTree a b) → (a ≥ 1)
CoprimeTreeᵣ-lower-bound : (CoprimeTree a b) → (b ≥ 2)

CoprimeTreeₗ-lower-bound leaf₁       = succ min
CoprimeTreeₗ-lower-bound leaf₂       = succ min
CoprimeTreeₗ-lower-bound (branch₁ t) = [≤]-predecessor (CoprimeTreeᵣ-lower-bound t)
CoprimeTreeₗ-lower-bound (branch₂ t) = [≤]-predecessor (CoprimeTreeᵣ-lower-bound t)
CoprimeTreeₗ-lower-bound (branch₃ t) = CoprimeTreeₗ-lower-bound t

CoprimeTreeᵣ-lower-bound leaf₁       = succ(succ min)
CoprimeTreeᵣ-lower-bound leaf₂       = succ(succ min)
CoprimeTreeᵣ-lower-bound {a}{_} (branch₁{b}{_} t) = subtransitivityᵣ(_≤_)(_≡_)  ([≤]-with-[+] ⦃ CoprimeTreeᵣ-lower-bound t ⦄ ⦃ min ⦄) (symmetry(_≡_) ([+][−₀]-almost-associativity {a}{a}{b} ([≤]-predecessor (CoprimeTree-order t))) 🝖 congruence₂-₁(_−₀_)(b) (commutativity(_⋅_) {a}{2}))
CoprimeTreeᵣ-lower-bound {a}{_} (branch₂{b}{_} t) = [≤]-with-[+] {2}{2 ⋅ a} ⦃ [⋅]ₗ-growing ([≤]-predecessor (CoprimeTreeᵣ-lower-bound t)) ⦄ {0}{b} ⦃ min ⦄
CoprimeTreeᵣ-lower-bound {a}{_} (branch₃{_}{b} t) = [≤]-with-[+] {0}{2 ⋅ a} ⦃ min ⦄ {2}{b} ⦃ CoprimeTreeᵣ-lower-bound t ⦄

CoprimeTree-correctness : (CoprimeTree a b) → (Coprime a b)
CoprimeTree-correctness        leaf₁ = Coprime-of-1
CoprimeTree-correctness        leaf₂ = Coprime-of-1
CoprimeTree-correctness {a}{_} (branch₁{c} p) =
  • (
    a + (a −₀ c) 🝖[ _≡_ ]-[ [+][−₀]-almost-associativity {a}{a}{c} prev-ord ]-sym
    (a + a) −₀ c 🝖[ _≡_ ]-[ congruence₂-₁(_−₀_)(c) (commutativity(_⋅_) {2}{a}) ]-sym
    (2 ⋅ a) −₀ c 🝖-end
  )
  • (
    CoprimeTree-correctness p ⇒
    Coprime c a               ⇒-[ symmetry(Coprime) ]
    Coprime a c               ⇒-[ Coprime-of-[−₀] prev-ord ]
    Coprime a (a −₀ c)        ⇒-[ Coprime-of-[+] ]
    Coprime a (a + (a −₀ c))  ⇒-end
  )
  ⇒₂-[ substitute₂-₂ᵣ(Coprime)(a) ]
  Coprime a ((2 ⋅ a) −₀ c)  ⇒-end
  where
    prev-ord : c ≤ a
    prev-ord = [≤]-predecessor (CoprimeTree-order p)
CoprimeTree-correctness {a}{_} (branch₂{c} p) =
  • (
    a + (a + c) 🝖[ _≡_ ]-[ associativity(_+_) {a}{a}{c} ]-sym
    (a + a) + c 🝖[ _≡_ ]-[ congruence₂-₁(_+_)(c) (commutativity(_⋅_) {a}{2}) ]
    (2 ⋅ a) + c 🝖-end
  )
  • (
    CoprimeTree-correctness p ⇒
    Coprime c a               ⇒-[ symmetry(Coprime) ]
    Coprime a c               ⇒-[ Coprime-of-[+] ]
    Coprime a (a + c)         ⇒-[ Coprime-of-[+] ]
    Coprime a (a + (a + c))   ⇒-end
  )
  ⇒₂-[ substitute₂-₂ᵣ(Coprime)(a) ]
  Coprime a (2 ⋅ a + c) ⇒-end
CoprimeTree-correctness {a}{_} (branch₃{_}{c} p) =
  • (
    a + (a + c) 🝖[ _≡_ ]-[ associativity(_+_) {a}{a}{c} ]-sym
    (a + a) + c 🝖[ _≡_ ]-[ congruence₂-₁(_+_)(c) (commutativity(_⋅_) {a}{2}) ]
    (2 ⋅ a) + c 🝖-end
  )
  • (
    CoprimeTree-correctness p ⇒
    Coprime a c               ⇒-[ Coprime-of-[+] ]
    Coprime a (a + c)         ⇒-[ Coprime-of-[+] ]
    Coprime a (a + (a + c))   ⇒-end
  )
  ⇒₂-[ substitute₂-₂ᵣ(Coprime)(a) ]
  Coprime a (2 ⋅ a + c) ⇒-end

-- TODO: Is this actually true? The Wikipedia article states this but without proof 
-- CoprimeTree-completeness : (a < b) → (Coprime a b) → (CoprimeTree a b)
-- CoprimeTree-completeness ord (intro p) = {!!}
