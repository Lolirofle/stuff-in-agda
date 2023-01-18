module Numeral.Natural.Function.GreatestCommonDivisor.Extended.Proofs where

import Lvl
open import Data
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Logic.Predicate
open import Numeral.Integer as ℤ
open import Numeral.Integer.Function using (−_)
open import Numeral.Integer.Oper using (_+_ ; _−_ ; _⋅_)
open import Numeral.Integer.Oper.Proofs
open import Numeral.Natural as ℕ
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Function.GreatestCommonDivisor.Algorithm
open import Numeral.Natural.Function.GreatestCommonDivisor.Extended
open import Numeral.Natural.Function.GreatestCommonDivisor.Proofs
import      Numeral.Natural.Oper as ℕ
open import Numeral.Natural.Oper.DivMod.Proofs
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.Modulo
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Multi
open import Structure.Operator
open import Structure.Operator.Properties
open import Syntax.Number
open import Syntax.Transitivity

private variable a b d : ℕ

-- TODO: This proof is unnecessarily unreadable because it includes the preservement of operators between ℕ and ℤ. Revise it when more operators have been defined in ℤ
-- Also called: Bézout's identity, extended Euclid's algorithm.
gcdExt-is-gcd-linearCombination : let (x , y) = gcdExt a b in (((+ₙ a) ⋅ x) + ((+ₙ b) ⋅ y) ≡ +ₙ(gcd a b))
gcdExt-is-gcd-linearCombination {a}{b} = gcdAlgorithmIntro (ℤ ⨯ ℤ) (\{a}{b} (x , y) → (((+ₙ a) ⋅ x) + ((+ₙ b) ⋅ y) ≡ +ₙ(gcd a b)))
  (\{a}{b} ab {(x , y)} prev →
    ((+ₙ a) ⋅ y) + ((+ₙ b) ⋅ (x − +ₙ(a ⌊/⌋ b) ⋅ y))                 🝖[ _≡_ ]-[ commutativity(_+_) {(+ₙ a) ⋅ y}{(+ₙ b) ⋅ (x − (+ₙ(a ⌊/⌋ b)) ⋅ y)} ]
    ((+ₙ b) ⋅ (x − (+ₙ(a ⌊/⌋ b) ⋅ y))) + ((+ₙ a) ⋅ y)               🝖[ _≡_ ]-[ congruence₂-₁(_+_)((+ₙ a) ⋅ y) (distributivityₗ(_⋅_)(_−_) {+ₙ b}) ]
    (((+ₙ b) ⋅ x) − ((+ₙ b) ⋅ (+ₙ(a ⌊/⌋ b) ⋅ y))) + ((+ₙ a) ⋅ y)    🝖[ _≡_ ]-[]
    (((+ₙ b) ⋅ x) + (−((+ₙ b) ⋅ (+ₙ(a ⌊/⌋ b) ⋅ y)))) + ((+ₙ a) ⋅ y) 🝖[ _≡_ ]-[ associativity(_+_) {(+ₙ b) ⋅ x}{_}{(+ₙ a) ⋅ y} ]
    ((+ₙ b) ⋅ x) + (−((+ₙ b) ⋅ (+ₙ(a ⌊/⌋ b) ⋅ y)) + ((+ₙ a) ⋅ y))   🝖[ _≡_ ]-[ congruence₂-₂(_+_)((+ₙ b) ⋅ x) (
      −((+ₙ b) ⋅ (+ₙ(a ⌊/⌋ b) ⋅ y)) + ((+ₙ a) ⋅ y) 🝖[ _≡_ ]-[ congruence₂-₁(_+_)((+ₙ a) ⋅ y) (congruence₁(−_) (associativity(_⋅_) {+ₙ b}{_}{y})) ]-sym
      −(((+ₙ b) ⋅ +ₙ(a ⌊/⌋ b)) ⋅ y) + ((+ₙ a) ⋅ y) 🝖[ _≡_ ]-[ congruence₂-₁(_+_)((+ₙ a) ⋅ y) ([−]-preserves-[⋅]ₗ {(+ₙ b) ⋅ (+ₙ(a ⌊/⌋ b))}{y}) ]-sym
      (−((+ₙ b) ⋅ +ₙ(a ⌊/⌋ b)) ⋅ y) + ((+ₙ a) ⋅ y) 🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(_+_) {−((+ₙ b) ⋅ (+ₙ(a ⌊/⌋ b)))}{+ₙ a} ]-sym
      (−((+ₙ b) ⋅ +ₙ(a ⌊/⌋ b)) + (+ₙ a)) ⋅ y       🝖[ _≡_ ]-[ congruence₂-₁(_⋅_)(y) (
        −((+ₙ b) ⋅ +ₙ(a ⌊/⌋ b)) + (+ₙ a)  🝖[ _≡_ ]-[ commutativity(_+_) {−((+ₙ b) ⋅ +ₙ(a ⌊/⌋ b))}{+ₙ a} ]
        (+ₙ a) − ((+ₙ b) ⋅ (+ₙ(a ⌊/⌋ b))) 🝖[ _≡_ ]-[ congruence₂-₂(_−_)(+ₙ a) (commutativity(_⋅_) {+ₙ b}{+ₙ(a ⌊/⌋ b)}) ]
        (+ₙ a) − ((+ₙ(a ⌊/⌋ b)) ⋅ (+ₙ b)) 🝖[ _≡_ ]-[ congruence₂-₂(_−_)(+ₙ a) (preserving₂(+ₙ_)(ℕ._⋅_)(_⋅_) {a ⌊/⌋ b}{b} ) ]-sym
        (+ₙ a) − +ₙ((a ⌊/⌋ b) ℕ.⋅ b)      🝖[ _≡_ ]-[ [+ₙ][−₀][−]-preserving {a}{(a ⌊/⌋ b) ℕ.⋅ b} ([⌊/⌋][⋅]-semiInverse-order {a}{b}) ]-sym
        +ₙ(a ℕ.−₀ ((a ⌊/⌋ b) ℕ.⋅ b))      🝖[ _≡_ ]-[ congruence₁(+ₙ_) ([⌊/⌋][⋅]-inverseOperatorᵣ-error {a}{b}) ]-sym
        +ₙ(a mod b)                       🝖-end
      )]
      +ₙ(a mod b) ⋅ y                              🝖[ _≡_ ]-end
    ) ]
    ((+ₙ b) ⋅ x) + (+ₙ(a mod b) ⋅ y)                                🝖[ _≡_ ]-[ prev ]
    +ₙ gcd b (a mod b)                                              🝖[ _≡_ ]-[ congruence₁(+ₙ_) (commutativity(gcd) {b}{a mod b}) ]
    +ₙ gcd (a mod b) b                                              🝖[ _≡_ ]-[ congruence₁(+ₙ_) (gcd-of-mod{a}{b}) ]
    +ₙ gcd a b                                                      🝖-end
  )
  (\{a} a0 →
    ((+ₙ a) ⋅ 1) + (0 ⋅ 0) 🝖[ _≡_ ]-[ congruence₂(_+_) (identityᵣ(_⋅_)(1) {+ₙ a}) (absorberᵣ(_⋅_)(0) {0}) ]
    (+ₙ a) + 0             🝖[ _≡_ ]-[ identityᵣ(_+_)(0) ]
    +ₙ a                   🝖[ _≡_ ]-[ congruence₁(+ₙ_) (identityᵣ(gcd)(0)) ]-sym
    +ₙ gcd a ℕ.𝟎           🝖-end
  )
  (\{a}{b}{(x , y)} ab prev →
    ((+ₙ b) ⋅ y) + ((+ₙ a) ⋅ x) 🝖[ _≡_ ]-[ commutativity(_+_) {(+ₙ b) ⋅ y}{(+ₙ a) ⋅ x} ]
    ((+ₙ a) ⋅ x) + ((+ₙ b) ⋅ y) 🝖[ _≡_ ]-[ prev ]
    +ₙ gcd a b                  🝖[ _≡_ ]-[ congruence₁(+ₙ_) (commutativity(gcd) {a}{b}) ]
    +ₙ gcd b a                  🝖-end
  )
  (\{a} →
    ((+ₙ a) ⋅ 1) + ((+ₙ a) ⋅ 0) 🝖[ _≡_ ]-[ congruence₂(_+_) (identityᵣ(_⋅_)(1) {+ₙ a}) (absorberᵣ(_⋅_)(0) {+ₙ a}) ]
    (+ₙ a) + 0                  🝖[ _≡_ ]-[ identityᵣ(_+_)(0) ]
    (+ₙ a)                      🝖[ _≡_ ]-[ congruence₁(+ₙ_) gcd-idempotence ]-sym
    +ₙ gcd a a                  🝖-end
  )
  a
  b

gcd-linearCombination-existence : ∃{Obj = ℤ ⨯ ℤ}(\{(x , y) → (((+ₙ a) ⋅ x) + ((+ₙ b) ⋅ y) ≡ +ₙ(gcd a b))})
gcd-linearCombination-existence{a}{b} = [∃]-intro (gcdExt a b) ⦃ gcdExt-is-gcd-linearCombination{a}{b} ⦄

{-
open import Logic.IntroInstances
open import Logic.Predicate
open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.DivMod.Proofs
open import Numeral.Natural.Oper.Modulo.Proofs
open import Relator.Equals
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Multi
open import Structure.Operator.Proofs.Util
open import Syntax.Function
open import Syntax.Transitivity

-- gcd-gcdExt-equal : (gcd a b ≡ Tuple.left(gcdExt a b))
-- gcd-gcdExt-equal {a}{b} = Gcd-unique {a}{b} Gcd-gcd Gcd-gcdFold

-- Also called: Bézout's identity, extended Euclid's algorithm.
gcd-linearCombination-existence : ∃{Obj = ℤ ⨯ ℤ}(\{(x , y) → (((+ₙ a) ⋅ x) + ((+ₙ b) ⋅ y) ≡ +ₙ(gcd a b))})
gcd-linearCombination-existence {a}{b} = ℕ-strong-induction(\b → (a : ℕ) → ∃{Obj = ℤ ⨯ ℤ}(\{(x , y) → (((+ₙ a) ⋅ x) + ((+ₙ b) ⋅ y) ≡ +ₙ(gcd a b))})) base step b a where
  base : (a : ℕ) → ∃{Obj = ℤ ⨯ ℤ}(\{(x , y) → (((+ₙ a) ⋅ x) + (0 ⋅ y) ≡ +ₙ(gcd a 0))})
  ∃.witness (base a)       = (1 , 0)
  ∃.proof   (base ℕ.𝟎)     = [≡]-intro
  ∃.proof   (base (ℕ.𝐒 a)) = [≡]-intro

  step : (i : ℕ) → ((j : ℕ) → (j ≤ i) → (a : ℕ) → ∃{Obj = ℤ ⨯ ℤ}(\{(x , y) → (((+ₙ a) ⋅ x) + ((+ₙ j) ⋅ y) ≡ +ₙ(gcd a j))})) → (a : ℕ) → ∃{Obj = ℤ ⨯ ℤ}(\{(x , y) → (((+ₙ a) ⋅ x) + ((+𝐒ₙ i) ⋅ y) ≡ +ₙ(gcd a (ℕ.𝐒(i))))})
  ∃.witness (step i prev a) with [≥]-or-[<] {a}{ℕ.𝐒(i)}
  ... | [∨]-introₗ ia with [∃]-intro (x , y) ← prev(a mod ℕ.𝐒(i)) ([≤]-without-[𝐒] (mod-maxᵣ {a = a})) (ℕ.𝐒(i)) = (y , ((x − ((+ₙ(a ⌊/⌋ ℕ.𝐒(i))) ⋅ y))))
  ... | [∨]-introᵣ (succ ai) with [∃]-intro (x , y) ← prev a ai (ℕ.𝐒(i)) = (y , x)
  ∃.proof (step i prev a) with [≥]-or-[<] {a}{ℕ.𝐒(i)}
  ... | [∨]-introₗ ia with [∃]-intro (x , y) ⦃ p ⦄ ← prev(a mod ℕ.𝐒(i)) ([≤]-without-[𝐒] (mod-maxᵣ {a = a})) (ℕ.𝐒(i)) =
    ((+ₙ a) ⋅ y) + ((+𝐒ₙ i) ⋅ (x − ((+ₙ(a ⌊/⌋ ℕ.𝐒(i))) ⋅ y)))             🝖[ _≡_ ]-[ congruence₂-₂(_+_)((+ₙ a) ⋅ y) (distributivityₗ(_⋅_)(_−_) {+𝐒ₙ i}{x}{(+ₙ(a ⌊/⌋ ℕ.𝐒(i))) ⋅ y}) ]
    ((+ₙ a) ⋅ y) + (((+𝐒ₙ i) ⋅ x) − ((+𝐒ₙ i) ⋅ ((+ₙ(a ⌊/⌋ ℕ.𝐒(i))) ⋅ y))) 🝖[ _≡_ ]-[ congruence₂-₂(_+_)((+ₙ a) ⋅ y) (congruence₂-₂(_−_)((+𝐒ₙ i) ⋅ x) p1) ]
    ((+ₙ a) ⋅ y) + (((+𝐒ₙ i) ⋅ x) − ((+ₙ(a ℕ.−₀ (a mod ℕ.𝐒(i)))) ⋅ y))    🝖[ _≡_ ]-[ One.commuteₗ-assocᵣ{a = (+ₙ a) ⋅ y}{b = (+𝐒ₙ i) ⋅ x} ]
    ((+𝐒ₙ i) ⋅ x) + (((+ₙ a) ⋅ y) − ((+ₙ(a ℕ.−₀ (a mod ℕ.𝐒(i)))) ⋅ y))    🝖[ _≡_ ]-[ congruence₂-₂(_+_)((+𝐒ₙ i) ⋅ x) (distributivityᵣ(_⋅_)(_−_) {+ₙ a}{_}{y}) ]-sym
    ((+𝐒ₙ i) ⋅ x) + (((+ₙ a) − (+ₙ(a ℕ.−₀ (a mod ℕ.𝐒(i))))) ⋅ y)          🝖[ _≡_ ]-[ congruence₂-₂(_+_)((+𝐒ₙ i) ⋅ x) (congruence₂-₁(_⋅_)(y) p2) ]
    ((+𝐒ₙ i) ⋅ x) + ((+ₙ(a mod ℕ.𝐒(i))) ⋅ y)                              🝖[ _≡_ ]-[ p ]
    +ₙ(gcd (ℕ.𝐒(i)) (a mod ℕ.𝐒(i)))                                       🝖-end
    where
      p0 =
        (ℕ.𝐒 i) ℕ.⋅ (a ⌊/⌋ ℕ.𝐒(i)) 🝖[ _≡_ ]-[ commutativity(ℕ._⋅_) {ℕ.𝐒 i}{a ⌊/⌋ ℕ.𝐒(i)} ]
        (a ⌊/⌋ ℕ.𝐒(i)) ℕ.⋅ (ℕ.𝐒 i) 🝖[ _≡_ ]-[ OneTypeTwoOp.moveᵣ-to-invOp {b = a mod ℕ.𝐒(i)}{c = a} (([⌊/⌋][mod]-is-division-with-remainder {y = ℕ.𝐒 i})) ]
        a ℕ.−₀ (a mod ℕ.𝐒(i))      🝖-end

      p1 =
        (+𝐒ₙ i) ⋅ ((+ₙ(a ⌊/⌋ ℕ.𝐒(i))) ⋅ y)     🝖[ _≡_ ]-[ associativity(_⋅_) {+𝐒ₙ i} ]-sym
        ((+𝐒ₙ i) ⋅ (+ₙ(a ⌊/⌋ ℕ.𝐒(i)))) ⋅ y     🝖[ _≡_ ]-[]
        ((+ₙ(ℕ.𝐒 i)) ⋅ (+ₙ(a ⌊/⌋ ℕ.𝐒(i)))) ⋅ y 🝖[ _≡_ ]-[ congruence₂-₁(_⋅_)(y) (preserving₂(+ₙ_)(ℕ._⋅_)(_⋅_) {ℕ.𝐒 i}) ]-sym
        (+ₙ((ℕ.𝐒 i) ℕ.⋅ (a ⌊/⌋ ℕ.𝐒(i)))) ⋅ y   🝖[ _≡_ ]-[ congruence₂-₁(_⋅_)(y) (congruence₁(+ₙ_) p0) ]
        (+ₙ(a ℕ.−₀ (a mod ℕ.𝐒(i)))) ⋅ y        🝖-end

      p2 =
        (+ₙ a) − (+ₙ(a ℕ.−₀ (a mod ℕ.𝐒(i))))          🝖[ _≡_ ]-[ congruence₂-₂(_−_)(+ₙ a) ([+ₙ][−₀][−]-preserving (mod-maxₗ {a}{ℕ.𝐒(i)})) ]
        (+ₙ a) − ((+ₙ a) − (+ₙ(a mod ℕ.𝐒(i))))        🝖[ _≡_ ]-[ congruence₂-₂(_+_)(+ₙ a) (preserving₂(−_)(_+_)(_+_) {+ₙ a}{−(+ₙ(a mod ℕ.𝐒(i)))}) ]
        (+ₙ a) + ((−(+ₙ a)) − (−(+ₙ(a mod ℕ.𝐒(i)))))  🝖[ _≡_ ]-[ associativity(_+_) {+ₙ a}{−(+ₙ a)} ]-sym
        ((+ₙ a) − (+ₙ a)) − (−(+ₙ(a mod ℕ.𝐒(i))))     🝖[ _≡_ ]-[ congruence₂(_+_) (inverseFunctionᵣ(_+_)(−_) {+ₙ a}) (involution(−_)) ]
        0 + (+ₙ(a mod ℕ.𝐒(i)))                        🝖[ _≡_ ]-[ identityₗ(_+_)(0) ]
        +ₙ(a mod ℕ.𝐒(i))                              🝖[ _≡_ ]-end
  ... | [∨]-introᵣ (succ ai) with [∃]-intro (x , y) ⦃ p ⦄ ← prev a ai (ℕ.𝐒(i)) = commutativity(_+_) {(+ₙ a) ⋅ y}{(+ₙ ℕ.𝐒(i)) ⋅ x} 🝖 p
-}

{-
open import Functional
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs

linear-combination-is-multiple-of-gcd : ∀{x y}{a b c} → (((+ₙ a) ⋅ x) + ((+ₙ b) ⋅ y) ≡ +ₙ c) → (gcd a b ∣ c)
linear-combination-is-multiple-of-gcd {x} {y} {a} {b} {c} eq
  with [∃]-intro p ⦃ gcdpa ⦄ ← [↔]-to-[←] divides-[⋅]-existence (Gcd.divisorₗ{a}{b} Gcd-gcd)
  with [∃]-intro q ⦃ gcdqb ⦄ ← [↔]-to-[←] divides-[⋅]-existence (Gcd.divisorᵣ{a}{b} Gcd-gcd)
  = [↔]-to-[→] divides-[⋅]-existence
    ([∃]-intro (absₙ(((+ₙ p) ⋅ x) + ((+ₙ q) ⋅ y))) ⦃ injective(+ₙ_) $
      (+ₙ ((gcd a b) ℕ.⋅ absₙ(((+ₙ p) ⋅ x) + ((+ₙ q) ⋅ y))))                 🝖[ _≡_ ]-[ {!!} ]
      (+ₙ (absₙ(((+ₙ((gcd a b) ℕ.⋅ p)) ⋅ x) + ((+ₙ((gcd a b) ℕ.⋅ q)) ⋅ y)))) 🝖[ _≡_ ]-[ {!!} ]
      (((+ₙ((gcd a b) ℕ.⋅ p)) ⋅ x) + ((+ₙ((gcd a b) ℕ.⋅ q)) ⋅ y))            🝖[ _≡_ ]-[ congruence₂(_+_) {!!} {!!} ]
      (((+ₙ a) ⋅ x) + ((+ₙ b) ⋅ y))                                          🝖[ _≡_ ]-[ eq ]
      (+ₙ c)                                                                 🝖-end
    ⦄)
-}
