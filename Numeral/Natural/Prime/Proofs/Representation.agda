module Numeral.Natural.Prime.Proofs.Representation where

open import Data.Boolean.Stmt
open import Data.List
open import Data.List.Functions as List using (_++_)
open import Functional as Fn using (_∘_)
import      Lang.Irrelevance.Squash as Irr
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Prime
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Divisibility
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Operator
open import Structure.Relator
open import Structure.Relator.Properties
open import Structure.Setoid.Uniqueness
open import Syntax.Function
open import Syntax.Implication
open import Syntax.Transitivity
open import Syntax.Type
open import Type

module _ where
  open import Data
  open import Data.Either as Either using ()
  open import Data.List.Equiv.Id
  open import Data.Tuple as Tuple using (_,_)
  open import Numeral.Natural.Oper.Comparisons
  open import Numeral.Natural.Oper.Proofs
  open import Numeral.Natural.Prime.Decidable
  open import Numeral.Natural.Prime.Proofs
  open import Numeral.Natural.Relation.Divisibility.Strict
  open import Structure.Operator.Properties
  open import Structure.Relator.Ordering

  -- Natural numbers greater than 1 have a prime sequence representation.
  -- Note: This proof is very similar to the proof of prime factor existence (prime-factor-existence).
  prime-representation-existence : ∀{n} → ⦃ IsTrue(n >? 1) ⦄ → ∃{Obj = List(∃(Irr.Squash ∘ Prime))}(l ↦ (n ≡ List.foldᵣ((_⋅_) ∘ [∃]-witness) 𝟏 l))
  prime-representation-existence {𝐒(𝐒 n)} = Strict.Properties.accessible-induction(_∣≢_) {P = \n → ⦃ IsTrue(n >? 1) ⦄ → ∃(l ↦ (n ≡ List.foldᵣ((_⋅_) ∘ [∃]-witness{Pred = Irr.Squash ∘ Prime}) 𝟏 l))} rec {𝐒(𝐒(n))} where
    rec : ∀{n} → ({prev : ℕ} ⦃ _ : prev ∣≢ n ⦄ → ⦃ IsTrue(prev >? 1) ⦄ → ∃(l ↦ (prev ≡ List.foldᵣ((_⋅_) ∘ [∃]-witness) 𝟏 l))) → ⦃ IsTrue(n >? 1) ⦄ → ∃(l ↦ (n ≡ List.foldᵣ((_⋅_) ∘ [∃]-witness) 𝟏 l))
    rec {n} prev with prime-or-composite{n}
    ... | Either.Left  prim = [∃]-intro (List.singleton([∃]-intro n ⦃ Irr.intro prim ⦄)) ⦃ [≡]-intro ⦄
    ... | Either.Right comp =
      let
        [∃]-intro(A , B) ⦃ p ⦄ = [↔]-to-[→] composite-existence comp
        a = 𝐒(𝐒(A))
        b = 𝐒(𝐒(B))        
        [∃]-intro da ⦃ pa ⦄ = prev{a} ⦃ substitute₂ᵣ(_∣≢_){a} p ([∣≢]-of-[⋅]ₗ {a}{b}) ⦄
        [∃]-intro db ⦃ pb ⦄ = prev{b} ⦃ substitute₂ᵣ(_∣≢_){b} p ([∣≢]-of-[⋅]ᵣ {a}{b}) ⦄
        pab =
          n                                                                           🝖[ _≡_ ]-[ p ]-sym
          a ⋅ b                                                                       🝖[ _≡_ ]-[ congruence₂(_⋅_) pa pb ]
          (List.foldᵣ((_⋅_) ∘ ∃.witness) 1 da) ⋅ (List.foldᵣ((_⋅_) ∘ ∃.witness) 1 db) 🝖[ _≡_ ]-[ foldᵣ-preserves-[++] {_▫₁_ = (_⋅_) ∘ [∃]-witness}{_▫₂_ = _⋅_}{1} {da}{db} (\{x}{y}{z} → associativity(_⋅_) {[∃]-witness x}{y}{z})  ]-sym
          List.foldᵣ((_⋅_) ∘ ∃.witness) 1 (da List.++ db)                             🝖-end
      in [∃]-intro (da List.++ db) ⦃ pab ⦄

module _ where
  open import Data.List.Relation.Membership using (_∈_)
  open import Data.List.Relation.Quantification
  open import Numeral.Natural.Relation.Divisibility.Proofs

  module _ where
    open import Numeral.Natural.Prime.Proofs
    open import Numeral.Natural.Relation.Divisibility.Proofs.Product

    prime-in-prime-list : ∀{p}{l} → Prime(p) → AllElements Prime(l) → (p ∣ List.foldᵣ(_⋅_) 1 l) → (p ∈ l)
    prime-in-prime-list {p} pp ∅ div with () ←
      • (div ⇒
        (p ∣ List.foldᵣ(_⋅_) 1 ∅) ⇒-[]
        (p ∣ 1)                   ⇒-[ [1]-only-divides-[1] ]
        (p ≡ 1)                   ⇒-end
      )
      • Prime(p) :-[ pp ]
      ⇒₂-[ substitute₁(Prime) ]
      Prime(1)                  ⇒-[ [1]-nonprime ]
      ⊥                         ⇒-end
    prime-in-prime-list {p}{x ⊰ l} pp (px ⊰ pl) div =
      • (
        (p ∣ x)                   ⇒-[ [∨]-elim (\{[≡]-intro → [⊥]-elim ([1]-nonprime pp)}) Fn.id ∘ prime-only-divisors px ]
        (p ≡ x)                   ⇒-[ •_ ]
        (p ∈ (x ⊰ l))             ⇒-end
      )
      • (
        (p ∣ List.foldᵣ(_⋅_) 1 l) ⇒-[ prime-in-prime-list {p}{l} pp (pl) ]
        (p ∈ l)                   ⇒-[ ⊰_ ]
        (p ∈ (x ⊰ l))             ⇒-end
      )
      • (div ⇒
        (p ∣ List.foldᵣ(_⋅_) 1 (x ⊰ l))     ⇒-[]
        (p ∣ x ⋅ List.foldᵣ(_⋅_) 1 l)       ⇒-[ prime-divides-of-[⋅] pp ]
        (p ∣ x) ∨ (p ∣ List.foldᵣ(_⋅_) 1 l) ⇒-end
      )
      ⇒₃-[ [∨]-elim ]
      (p ∈ (x ⊰ l)) ⇒-end

  open import Data.List.Relation.Membership.Functions
  open import Data.List.Relation.Membership.Proofs
  open import Data.List.Relation.Permutation
  open import Data.List.Relation.Permutation.Proofs
  open import Numeral.Natural.Relation.Divisibility.Proofs.List
  open import Numeral.Natural.Oper.FlooredDivision
  open import Numeral.Natural.Oper.FlooredDivision.Proofs.Compatibility
  open import Numeral.Natural.Oper.FlooredDivision.Proofs.Inverse

  -- TODO: Generalize
  foldᵣ-[⋅]-preserves-division : ∀{x}{l} ⦃ pos : Positive(x) ⦄ → (xl : x ∈ l) → (List.foldᵣ(_⋅_) 1 (without l xl) ≡ List.foldᵣ(_⋅_) 1 l ⌊/⌋ x)
  foldᵣ-[⋅]-preserves-division {x} (•_ {y}{l} p) =
    List.foldᵣ _⋅_ 1 (without (y ⊰ l) (• p)) 🝖[ _≡_ ]-[]
    List.foldᵣ _⋅_ 1 l                       🝖[ _≡_ ]-[ [⌊/⌋][swap⋅]-inverseOperatorᵣ {x} ]-sym
    (x ⋅ List.foldᵣ _⋅_ 1 l) ⌊/⌋ x           🝖[ _≡_ ]-[ congruence₁(_⌊/⌋ x) (congruence₂-₁(_⋅_)(List.foldᵣ(_⋅_)(1) l) p) ]
    (y ⋅ List.foldᵣ _⋅_ 1 l) ⌊/⌋ x           🝖[ _≡_ ]-[]
    List.foldᵣ _⋅_ 1 (y ⊰ l) ⌊/⌋ x           🝖-end
  foldᵣ-[⋅]-preserves-division {x} (⊰_ {l}{y} p) =
    List.foldᵣ(_⋅_) 1 (without (y ⊰ l) (⊰ p)) 🝖[ _≡_ ]-[]
    y ⋅ List.foldᵣ(_⋅_) 1 (without l p)       🝖[ _≡_ ]-[ congruence₂-₂(_⋅_)(y) (foldᵣ-[⋅]-preserves-division p) ]
    y ⋅ (List.foldᵣ(_⋅_) 1 l ⌊/⌋ x)           🝖[ _≡_ ]-[ [⌊/⌋][⋅]ᵣ-compatibility{y} (divides-[⋅]-list p) ]-sym
    (y ⋅ List.foldᵣ(_⋅_) 1 l) ⌊/⌋ x           🝖[ _≡_ ]-[]
    List.foldᵣ(_⋅_) 1 (y ⊰ l) ⌊/⌋ x           🝖-end

  open import Numeral.Natural.Prime.Proofs

  -- A variant of prime representation uniqueness.
  foldᵣ-primes-permutation : ∀{a b} → AllElements Prime(a) → AllElements Prime(b) → (List.foldᵣ(_⋅_) 1 a ≡ List.foldᵣ(_⋅_) 1 b) → (a permutes b)
  foldᵣ-primes-permutation {∅}     {∅} apa        apb eq = _permutes_.empty
  foldᵣ-primes-permutation {a ⊰ al}{∅} (pa ⊰ apa) apb eq with () ←
    • List.foldᵣ(_⋅_) 1 (a ⊰ al) ≡ List.foldᵣ(_⋅_) 1 ∅ :-[ eq ]
    • a ∣ a ⋅ List.foldᵣ(_⋅_) 1 al                     :-[ divides-with-[⋅] {c = List.foldᵣ(_⋅_) 1 al} ([∨]-introₗ (reflexivity(_∣_))) ]
    ⇒₂-[ substitute₂ᵣ(_∣_){a} ]
    (a ∣ List.foldᵣ(_⋅_) 1 ∅) ⇒-[]
    (a ∣ 1)                   ⇒-[ prime-in-prime-list pa apb ]
    (a ∈ ∅)                   ⇒-[ [∉]-empty ]
    ⊥                         ⇒-end
  foldᵣ-primes-permutation {a}{b ⊰ bl} apa (pb ⊰ apb) eq =
    a                  🝖[ _permutes_ ]-[ prepend-without-inverse-permutes ba ]
    b ⊰ (without a ba) 🝖[ _permutes_ ]-[ _permutes_.prepend without-left-permutes-right ]
    b ⊰ bl             🝖-end
    where
      ba : (b ∈ a)
      ba =
        • Prime(b)             :-[ pb ]
        • AllElements Prime(a) :-[ apa ]
        • (
          • List.foldᵣ(_⋅_)(1) (b ⊰ bl) ≡ List.foldᵣ(_⋅_)(1) a :-[ symmetry(_≡_) eq ]
          • b ∣ (b ⋅ List.foldᵣ _⋅_ 1 bl)                      :-[ divides-with-[⋅] {c = List.foldᵣ(_⋅_) 1 bl} ([∨]-introₗ (reflexivity(_∣_))) ]
          ⇒₂-[ substitute₂ᵣ(_∣_){b} ]
          b ∣ List.foldᵣ(_⋅_)(1) a ⇒-end
        )
        ⇒₃-[ prime-in-prime-list ]
        b ∈ a ⇒-end
  
      instance
        pos-b : Positive(b)
        pos-b = prime-positive pb

      without-left-permutes-right : (without a ba) permutes bl
      without-left-permutes-right =
        • (apa ⇒
          AllElements Prime a               ⇒-[ AllElements-without ba ]
          AllElements Prime (without a ba)  ⇒-end
        )
        • AllElements Prime bl              :-[ apb ]
        • (
          List.foldᵣ(_⋅_)(1) (without a ba) 🝖[ _≡_ ]-[ foldᵣ-[⋅]-preserves-division ba ]
          List.foldᵣ(_⋅_)(1) a ⌊/⌋ b        🝖[ _≡_ ]-[ congruence₁(_⌊/⌋ b) eq ]
          (b ⋅ List.foldᵣ(_⋅_)(1) bl) ⌊/⌋ b 🝖[ _≡_ ]-[ [⌊/⌋][swap⋅]-inverseOperatorᵣ {b} ]
          List.foldᵣ(_⋅_)(1) bl             🝖-end
        )
        ⇒₃-[ foldᵣ-primes-permutation {without _ ba} {bl} ]
        (without a ba) permutes bl          ⇒-end

module _ where
  open import Data.List.Proofs
  open import Data.List.Relation.Permutation
  open import Data.List.Relation.Permutation.Proofs
  open import Data.List.Relation.Quantification
  open import Data.List.Relation.Quantification.Proofs
  open import Lang.Irrelevance.Convertable
  open import Logic.Predicate.Proofs
  open import Numeral.Natural.Prime.Decidable
  open import Structure.Function.Domain

  prime-representation-uniqueness : ∀{n} → Unique{Obj = List(∃(Irr.Squash ∘ Prime))} ⦃ permutes-equiv ⦄ (l ↦ (n ≡ List.foldᵣ((_⋅_) ∘ [∃]-witness) 𝟏 l))
  prime-representation-uniqueness {n} {x = xl} {y = yl} px py =
    • (
      AllElements-[∃]-proof ⇒
      AllElements (Irr.Squash ∘ Prime ∘ [∃]-witness) (xl)        ⇒-[ AllElements-mapᵣ [∃]-witness Fn.id ]
      AllElements (Irr.Squash ∘ Prime) (List.map [∃]-witness xl) ⇒-[ AllElements-map [∃]-witness [∃]-witness (\p → Irr.Squash.obj p ⦃ decider-convertable ⦄) ]
      AllElements Prime(List.map [∃]-witness xl)                 ⇒-end
    )
    • (
      AllElements-[∃]-proof ⇒
      AllElements (Irr.Squash ∘ Prime ∘ [∃]-witness) (yl)        ⇒-[ AllElements-mapᵣ [∃]-witness Fn.id ]
      AllElements (Irr.Squash ∘ Prime) (List.map [∃]-witness yl) ⇒-[ AllElements-map [∃]-witness [∃]-witness (\p → Irr.Squash.obj p ⦃ decider-convertable ⦄) ]
      AllElements Prime(List.map [∃]-witness yl)                 ⇒-end
    )
    • (
      List.foldᵣ(_⋅_) 𝟏 (List.map [∃]-witness xl) 🝖[ _≡_ ]-[ foldᵣ-map-preserve{_▫_ = _⋅_}{l = xl} ]-sym
      List.foldᵣ((_⋅_) ∘ [∃]-witness) 𝟏 xl        🝖[ _≡_ ]-[ px ]-sym
      n                                           🝖[ _≡_ ]-[ py ]
      List.foldᵣ((_⋅_) ∘ [∃]-witness) 𝟏 yl        🝖[ _≡_ ]-[ foldᵣ-map-preserve{_▫_ = _⋅_}{l = yl} ]
      List.foldᵣ(_⋅_) 𝟏 (List.map [∃]-witness yl) 🝖-end
    )
    ⇒₃-[ foldᵣ-primes-permutation ]
    (List.map [∃]-witness xl) permutes (List.map [∃]-witness yl) ⇒-[ injective ⦃ _ ⦄ ⦃ _ ⦄ (List.map [∃]-witness) ⦃ permutes-map-injective ⦃ [∃]-witness-injective ⦄ ⦄ ]
    xl permutes yl                                               ⇒-end

  -- Each positive number have a corresponding finite multiset of prime numbers such that it is equal to the product of the numbers in the multiset.
  -- Examples:
  --   n = (p₁ ^ n₁) ⋅ (p₂ ^ n₂) ⋅ … ⋅ (pₖ ^ nₖ)
  -- Also called:
  -- • Fundamental theorem of arithmetic.
  -- • Canonical representation of positive integers by primes.
  -- • Unique prime factorization theorem.
  prime-representation : ∀{n} → ⦃ IsTrue(n >? 1) ⦄ → ∃!{Obj = List(∃(Irr.Squash ∘ Prime))} ⦃ permutes-equiv ⦄ (l ↦ (n ≡ List.foldᵣ((_⋅_) ∘ [∃]-witness) 𝟏 l))
  prime-representation = [∧]-intro prime-representation-existence prime-representation-uniqueness

-- TODO: This also means that this is a bijection between List(∃ Prime) and ℕ, and also between List(ℕ) and ℕ if one is successful in proving that there are countably infinite many primes (a constructive proof of the latter)
