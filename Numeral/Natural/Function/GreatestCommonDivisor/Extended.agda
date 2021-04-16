module Numeral.Natural.Function.GreatestCommonDivisor.Extended where

import Lvl
open import Data
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Logic.Propositional
open import Numeral.Integer as ℤ
open import Numeral.Integer.Oper
open import Numeral.Integer.Proofs hiding (_≤_)
open import Numeral.Natural as ℕ
open import Numeral.Natural.Function.GreatestCommonDivisor
import      Numeral.Natural.Oper as ℕ
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Classical
open import Syntax.Number
open import Type

-- TODO: Does the same algorithm work in the naturals? https://math.stackexchange.com/questions/237372/finding-positive-b%C3%A9zout-coefficients https://math.stackexchange.com/questions/1230224/positive-solutions-of-893x-2432y-19?rq=1
gcdExt : ℕ → ℕ → (ℕ ⨯ ℤ ⨯ ℤ)
gcdExt a b = gcdFold(\{a (𝐒 b) _ (succ min) _ (x , y) → (y , (x − ((+ₙ(a ⌊/⌋ ℕ.𝐒(b))) ⋅ y)))}) (\_ _ _ _ _ → Tuple.swap) (1 , 0) a b

open import Logic.IntroInstances
open import Logic.Predicate
open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.DivMod.Proofs
open import Numeral.Natural.Oper.Modulo.Proofs
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Multi
open import Structure.Operator
open import Structure.Operator.Proofs.Util
open import Structure.Operator.Properties
open import Syntax.Function
open import Syntax.Transitivity

private variable a b d : ℕ

gcd-gcdExt-equal : (gcd a b ≡ Tuple.left(gcdExt a b))
gcd-gcdExt-equal {a}{b} = Gcd-unique {a}{b} Gcd-gcd Gcd-gcdFold

-- Also called: Bézout's identity, extended Euclid's algorithm.
gcd-linearCombination-existence : ∃{Obj = ℤ ⨯ ℤ}(\{(x , y) → (((+ₙ a) ⋅ x) + ((+ₙ b) ⋅ y) ≡ +ₙ(gcd a b))})
gcd-linearCombination-existence {a}{b} = [ℕ]-strong-induction {φ = b ↦ ∀{a} → ∃{Obj = ℤ ⨯ ℤ}(\{(x , y) → (((+ₙ a) ⋅ x) + ((+ₙ b) ⋅ y) ≡ +ₙ(gcd a b))})} base step {b}{a} where
  base : ∀{a} → ∃{Obj = ℤ ⨯ ℤ}(\{(x , y) → (((+ₙ a) ⋅ x) + (0 ⋅ y) ≡ +ₙ(gcd a 0))})
  ∃.witness (base {a})     = (1 , 0)
  ∃.proof   (base {ℕ.𝟎})   = [≡]-intro
  ∃.proof   (base {ℕ.𝐒 a}) = [≡]-intro

  step : ∀{i} → (∀{j} → (j ≤ i) → ∀{a} → ∃{Obj = ℤ ⨯ ℤ}(\{(x , y) → (((+ₙ a) ⋅ x) + ((+ₙ j) ⋅ y) ≡ +ₙ(gcd a j))})) → ∀{a} → ∃{Obj = ℤ ⨯ ℤ}(\{(x , y) → (((+ₙ a) ⋅ x) + ((+𝐒ₙ i) ⋅ y) ≡ +ₙ(gcd a (ℕ.𝐒(i))))})
  ∃.witness (step {i} prev {a}) with [≥]-or-[<] {a}{ℕ.𝐒(i)}
  ... | [∨]-introₗ ia with [∃]-intro (x , y) ← prev{a mod ℕ.𝐒(i)} ([≤]-without-[𝐒] (mod-maxᵣ {a = a})) {ℕ.𝐒(i)} = (y , ((x − ((+ₙ(a ⌊/⌋ ℕ.𝐒(i))) ⋅ y))))
  ... | [∨]-introᵣ (succ ai) with [∃]-intro (x , y) ← prev{a} ai {ℕ.𝐒(i)} = (y , x)
  ∃.proof (step {i} prev {a}) with [≥]-or-[<] {a}{ℕ.𝐒(i)}
  ... | [∨]-introₗ ia with [∃]-intro (x , y) ⦃ p ⦄ ← prev{a mod ℕ.𝐒(i)} ([≤]-without-[𝐒] (mod-maxᵣ {a = a})) {ℕ.𝐒(i)} =
    ((+ₙ a) ⋅ y) + ((+𝐒ₙ i) ⋅ (x − ((+ₙ(a ⌊/⌋ ℕ.𝐒(i))) ⋅ y)))             🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)((+ₙ a) ⋅ y) (distributivityₗ(_⋅_)(_−_) {+𝐒ₙ i}{x}{(+ₙ(a ⌊/⌋ ℕ.𝐒(i))) ⋅ y}) ]
    ((+ₙ a) ⋅ y) + (((+𝐒ₙ i) ⋅ x) − ((+𝐒ₙ i) ⋅ ((+ₙ(a ⌊/⌋ ℕ.𝐒(i))) ⋅ y))) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)((+ₙ a) ⋅ y) (congruence₂ᵣ(_−_)((+𝐒ₙ i) ⋅ x) p1) ]
    ((+ₙ a) ⋅ y) + (((+𝐒ₙ i) ⋅ x) − ((+ₙ(a ℕ.−₀ (a mod ℕ.𝐒(i)))) ⋅ y))    🝖[ _≡_ ]-[ One.commuteₗ-assocᵣ{a = (+ₙ a) ⋅ y}{b = (+𝐒ₙ i) ⋅ x} ]
    ((+𝐒ₙ i) ⋅ x) + (((+ₙ a) ⋅ y) − ((+ₙ(a ℕ.−₀ (a mod ℕ.𝐒(i)))) ⋅ y))    🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)((+𝐒ₙ i) ⋅ x) (distributivityᵣ(_⋅_)(_−_) {+ₙ a}{_}{y}) ]-sym
    ((+𝐒ₙ i) ⋅ x) + (((+ₙ a) − (+ₙ(a ℕ.−₀ (a mod ℕ.𝐒(i))))) ⋅ y)          🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)((+𝐒ₙ i) ⋅ x) (congruence₂ₗ(_⋅_)(y) p2) ]
    ((+𝐒ₙ i) ⋅ x) + ((+ₙ(a mod ℕ.𝐒(i))) ⋅ y)                              🝖[ _≡_ ]-[ p ]
    +ₙ(gcd (ℕ.𝐒(i)) (a mod ℕ.𝐒(i)))                                       🝖-end
    where
      p0 =
        (ℕ.𝐒 i) ℕ.⋅ (a ⌊/⌋ ℕ.𝐒(i)) 🝖[ _≡_ ]-[ commutativity(ℕ._⋅_) {ℕ.𝐒 i}{a ⌊/⌋ ℕ.𝐒(i)} ]
        (a ⌊/⌋ ℕ.𝐒(i)) ℕ.⋅ (ℕ.𝐒 i) 🝖[ _≡_ ]-[ OneTypeTwoOp.moveᵣ-to-invOp {b = a mod ℕ.𝐒(i)}{c = a} (([⌊/⌋][mod]-is-division-with-remainder {y = i})) ]
        a ℕ.−₀ (a mod ℕ.𝐒(i))      🝖-end

      p1 =
        (+𝐒ₙ i) ⋅ ((+ₙ(a ⌊/⌋ ℕ.𝐒(i))) ⋅ y)     🝖[ _≡_ ]-[ associativity(_⋅_) {+𝐒ₙ i} ]-sym
        ((+𝐒ₙ i) ⋅ (+ₙ(a ⌊/⌋ ℕ.𝐒(i)))) ⋅ y     🝖[ _≡_ ]-[]
        ((+ₙ(ℕ.𝐒 i)) ⋅ (+ₙ(a ⌊/⌋ ℕ.𝐒(i)))) ⋅ y 🝖[ _≡_ ]-[ congruence₂ₗ(_⋅_)(y) (preserving₂(+ₙ_)(ℕ._⋅_)(_⋅_) {ℕ.𝐒 i}) ]-sym
        (+ₙ((ℕ.𝐒 i) ℕ.⋅ (a ⌊/⌋ ℕ.𝐒(i)))) ⋅ y   🝖[ _≡_ ]-[ congruence₂ₗ(_⋅_)(y) (congruence₁(+ₙ_) p0) ]
        (+ₙ(a ℕ.−₀ (a mod ℕ.𝐒(i)))) ⋅ y        🝖-end

      p2 =
        (+ₙ a) − (+ₙ(a ℕ.−₀ (a mod ℕ.𝐒(i))))          🝖[ _≡_ ]-[ congruence₂ᵣ(_−_)(+ₙ a) ([+ₙ][−₀][−]-preserving (mod-maxₗ {a}{ℕ.𝐒(i)})) ]
        (+ₙ a) − ((+ₙ a) − (+ₙ(a mod ℕ.𝐒(i))))        🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(+ₙ a) (preserving₂(−_)(_+_)(_+_) {+ₙ a}{−(+ₙ(a mod ℕ.𝐒(i)))}) ]
        (+ₙ a) + ((−(+ₙ a)) − (−(+ₙ(a mod ℕ.𝐒(i)))))  🝖[ _≡_ ]-[ associativity(_+_) {+ₙ a}{−(+ₙ a)} ]-sym
        ((+ₙ a) − (+ₙ a)) − (−(+ₙ(a mod ℕ.𝐒(i))))     🝖[ _≡_ ]-[ congruence₂(_+_) (inverseFunctionᵣ(_+_)(−_) {+ₙ a}) (involution(−_)) ]
        0 + (+ₙ(a mod ℕ.𝐒(i)))                        🝖[ _≡_ ]-[ identityₗ(_+_)(0) ]
        +ₙ(a mod ℕ.𝐒(i))                              🝖[ _≡_ ]-end
  ... | [∨]-introᵣ (succ ai) with [∃]-intro (x , y) ⦃ p ⦄ ← prev{a} ai {ℕ.𝐒(i)} = commutativity(_+_) {(+ₙ a) ⋅ y}{(+ₙ ℕ.𝐒(i)) ⋅ x} 🝖 p
