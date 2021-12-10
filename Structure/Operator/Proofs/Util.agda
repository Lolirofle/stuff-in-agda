module Structure.Operator.Proofs.Util where

import Lvl
open import Data
open import Data.Tuple
open import Functional hiding (id)
open import Function.Equals
import      Function.Names as Names
import      Lang.Vars.Structure.Operator
open        Lang.Vars.Structure.Operator.Select
open import Logic.IntroInstances
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Function.Domain
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

module One {ℓ ℓₑ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {_▫_ : T → T → T} where
  open Lang.Vars.Structure.Operator.One ⦃ equiv = equiv ⦄ {_▫_ = _▫_}

  -- TODO: Rename this to associate-commute4-commuting
  -- TODO: Also https://en.wikipedia.org/wiki/Medial_magma https://math.stackexchange.com/questions/609364/why-is-ring-addition-commutative?noredirect=1&lq=1
  associate-commute4 : let _ = op , assoc in ∀{a b c d} → Names.Commuting(_▫_)(b)(c) → ((a ▫ b) ▫ (c ▫ d) ≡ (a ▫ c) ▫ (b ▫ d))
  associate-commute4 {a}{b}{c}{d} com =
    (a ▫ b) ▫ (c ▫ d) 🝖-[ symmetry(_≡_) (associativity(_▫_) {a ▫ b} {c} {d}) ]
    ((a ▫ b) ▫ c) ▫ d 🝖-[ congruence₂-₁(_▫_)(d) (associativity(_▫_) {a} {b} {c}) ]
    (a ▫ (b ▫ c)) ▫ d 🝖-[ (congruence₂-₁(_▫_)(d) ∘ congruence₂-₂(_▫_)(a)) com ]
    (a ▫ (c ▫ b)) ▫ d 🝖-[ associativity(_▫_) {a} {c ▫ b} {d} ]
    a ▫ ((c ▫ b) ▫ d) 🝖-[ congruence₂-₂(_▫_)(a) (associativity(_▫_) {c} {b} {d}) ]
    a ▫ (c ▫ (b ▫ d)) 🝖-[ symmetry(_≡_) (associativity(_▫_) {a} {c} {b ▫ d}) ]
    (a ▫ c) ▫ (b ▫ d) 🝖-end

  -- TODO: Rename this to associate-commute4
  associate-commute4-c : let _ = op , assoc , comm in ∀{a b c d} → ((a ▫ b) ▫ (c ▫ d) ≡ (a ▫ c) ▫ (b ▫ d))
  associate-commute4-c = associate-commute4(commutativity(_▫_))

  associate4-123-321 : let _ = op , assoc in ∀{a b c d} → (((a ▫ b) ▫ c) ▫ d ≡ a ▫ (b ▫ (c ▫ d)))
  associate4-123-321 {a}{b}{c}{d} = associativity(_▫_) 🝖 associativity(_▫_)

  associate4-123-213 : let _ = op , assoc in ∀{a b c d} → (((a ▫ b) ▫ c) ▫ d ≡ (a ▫ (b ▫ c)) ▫ d)
  associate4-123-213 {a}{b}{c}{d} = congruence₂-₁(_▫_)(_) (associativity(_▫_))

  associate4-321-231 : let _ = op , assoc in ∀{a b c d} → (a ▫ (b ▫ (c ▫ d)) ≡ a ▫ ((b ▫ c) ▫ d))
  associate4-321-231 {a}{b}{c}{d} = congruence₂-₂(_▫_)(_) (symmetry(_≡_) (associativity(_▫_)))

  associate4-231-222 : let _ = op , assoc in ∀{a b c d} → (a ▫ ((b ▫ c) ▫ d) ≡ (a ▫ b) ▫ (c ▫ d))
  associate4-231-222 {a}{b}{c}{d} = symmetry(_≡_) associate4-321-231 🝖 symmetry(_≡_) associate4-123-321 🝖 associativity(_▫_)

  associate4-213-222 : let _ = op , assoc in ∀{a b c d} → ((a ▫ (b ▫ c)) ▫ d ≡ (a ▫ b) ▫ (c ▫ d))
  associate4-213-222 {a}{b}{c}{d} = associativity(_▫_) 🝖 associate4-231-222

  associate4-321-222 : let _ = op , assoc in ∀{a b c d} → (a ▫ (b ▫ (c ▫ d)) ≡ (a ▫ b) ▫ (c ▫ d))
  associate4-321-222 {a}{b}{c}{d} = associate4-321-231 🝖 associate4-231-222

  commuteᵣ-assocₗ : let _ = op , assoc , comm in ∀{a b c} → (((a ▫ b) ▫ c) ≡ ((a ▫ c) ▫ b))
  commuteᵣ-assocₗ {a}{b}{c} =
    (a ▫ b) ▫ c 🝖-[ associativity(_▫_) ]
    a ▫ (b ▫ c) 🝖-[ congruence₂-₂(_▫_)(_) (commutativity(_▫_)) ]
    a ▫ (c ▫ b) 🝖-[ associativity(_▫_) ]-sym
    (a ▫ c) ▫ b 🝖-end

  commuteₗ-assocᵣ : let _ = op , assoc , comm in ∀{a b c} → ((a ▫ (b ▫ c)) ≡ (b ▫ (a ▫ c)))
  commuteₗ-assocᵣ {a}{b}{c} =
    a ▫ (b ▫ c) 🝖-[ associativity(_▫_) ]-sym
    (a ▫ b) ▫ c 🝖-[ congruence₂-₁(_▫_)(_) (commutativity(_▫_)) ]
    (b ▫ a) ▫ c 🝖-[ associativity(_▫_) ]
    b ▫ (a ▫ c) 🝖-end

  commuteₗ-assocₗ : let _ = op , assoc , comm in ∀{a b c} → (((a ▫ b) ▫ c) ≡ ((b ▫ c) ▫ a))
  commuteₗ-assocₗ {a}{b}{c} =
    (a ▫ b) ▫ c 🝖-[ associativity(_▫_) ]
    a ▫ (b ▫ c) 🝖-[ commutativity(_▫_) ]
    (b ▫ c) ▫ a 🝖-end

  commuteᵣ-assocᵣ : let _ = op , assoc , comm in ∀{a b c} → ((a ▫ (b ▫ c)) ≡ ((a ▫ c) ▫ b))
  commuteᵣ-assocᵣ = symmetry(_≡_) (associativity(_▫_)) 🝖 commuteᵣ-assocₗ

  -- TODO: Rename and generalize this (See commuteBoth in Structure.Operator.Properties)
  commuteBothTemp : let _ = comm in ∀{a₁ a₂ b₁ b₂} → (a₁ ▫ a₂ ≡ b₁ ▫ b₂) → (a₂ ▫ a₁ ≡ b₂ ▫ b₁)
  commuteBothTemp {a₁} {a₂} {b₁} {b₂} p =
    a₂ ▫ a₁ 🝖-[ commutativity(_▫_) ]-sym
    a₁ ▫ a₂ 🝖-[ p ]
    b₁ ▫ b₂ 🝖-[ commutativity(_▫_) ]
    b₂ ▫ b₁ 🝖-end

  moveₗ-to-inv : let _ = op , assoc , select-invₗ(idₗ)(identₗ)(invₗ)(inverₗ) in ∀{a b c} → (a ▫ b ≡ c) → (b ≡ invₗ(a) ▫ c)
  moveₗ-to-inv {idₗ = idₗ} {invₗ = invₗ} {a = a} {b} {c} abc =
    b                🝖-[ identityₗ(_▫_)(idₗ) ]-sym
    idₗ ▫ b          🝖-[ congruence₂-₁(_▫_)(b) (inverseFunctionₗ(_▫_)(invₗ)) ]-sym
    (invₗ a ▫ a) ▫ b 🝖-[ associativity(_▫_) ]
    invₗ a ▫ (a ▫ b) 🝖-[ congruence₂-₂(_▫_)(invₗ a) abc ]
    invₗ a ▫ c       🝖-end

  moveᵣ-to-inv : let _ = op , assoc , select-invᵣ(idᵣ)(identᵣ)(invᵣ)(inverᵣ) in ∀{a b c} → (a ▫ b ≡ c) → (a ≡ c ▫ invᵣ(b))
  moveᵣ-to-inv {idᵣ = idᵣ} {invᵣ = invᵣ} {a = a} {b} {c} abc =
    a                🝖-[ identityᵣ(_▫_)(idᵣ) ]-sym
    a ▫ idᵣ          🝖-[ congruence₂-₂(_▫_)(a) (inverseFunctionᵣ(_▫_)(invᵣ)) ]-sym
    a ▫ (b ▫ invᵣ b) 🝖-[ associativity(_▫_) ]-sym
    (a ▫ b) ▫ invᵣ b 🝖-[ congruence₂-₁(_▫_)(invᵣ b) abc ]
    c ▫ invᵣ b       🝖-end

  moveₗ-from-inv : let _ = op , assoc , select-idₗ(id)(identₗ) , select-invᵣ(id)(identᵣ)(invᵣ)(inverᵣ) in ∀{a b c} → (a ▫ b ≡ c) ← (b ≡ invᵣ(a) ▫ c)
  moveₗ-from-inv {id = id} {invᵣ = invᵣ} {a = a} {b} {c} bac =
    a ▫ b            🝖-[ congruence₂-₂(_▫_)(a) bac ]
    a ▫ (invᵣ a ▫ c) 🝖-[ associativity(_▫_) ]-sym
    (a ▫ invᵣ a) ▫ c 🝖-[ congruence₂-₁(_▫_)(c) (inverseFunctionᵣ(_▫_)(invᵣ)) ]
    id ▫ c           🝖-[ identityₗ(_▫_)(id) ]
    c                🝖-end

  moveᵣ-from-inv : let _ = op , assoc , select-idᵣ(id)(identᵣ) , select-invₗ(id)(identₗ)(invₗ)(inverₗ) in ∀{a b c} → (a ▫ b ≡ c) ← (a ≡ c ▫ invₗ(b))
  moveᵣ-from-inv {id = id} {invₗ = invₗ} {a = a} {b} {c} acb =
    a ▫ b            🝖-[ congruence₂-₁(_▫_)(b) acb ]
    (c ▫ invₗ b) ▫ b 🝖-[ associativity(_▫_) ]
    c ▫ (invₗ b ▫ b) 🝖-[ congruence₂-₂(_▫_)(c) (inverseFunctionₗ(_▫_)(invₗ)) ]
    c ▫ id           🝖-[ identityᵣ(_▫_)(id) ]
    c                🝖-end

module OneTypeTwoOp {ℓ ℓₑ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {_▫₁_ _▫₂_ : T → T → T} where
  open Lang.Vars.Structure.Operator.OneTypeTwoOp ⦃ equiv = equiv ⦄ {_▫₁_ = _▫₁_} {_▫₂_ = _▫₂_}

  cross-distribute : let _ = op₂ , distriₗ , distriᵣ in ∀{a b c d} → (a ▫₂ b) ▫₁ (c ▫₂ d) ≡ ((a ▫₁ c) ▫₂ (b ▫₁ c)) ▫₂ ((a ▫₁ d) ▫₂ (b ▫₁ d))
  cross-distribute {a = a}{b}{c}{d} =
    (a ▫₂ b) ▫₁ (c ▫₂ d)                             🝖-[ distributivityₗ(_▫₁_)(_▫₂_) ]
    ((a ▫₂ b) ▫₁ c) ▫₂ ((a ▫₂ b) ▫₁ d)               🝖-[ congruence₂(_▫₂_) (distributivityᵣ(_▫₁_)(_▫₂_)) (distributivityᵣ(_▫₁_)(_▫₂_)) ]
    ((a ▫₁ c) ▫₂ (b ▫₁ c)) ▫₂ ((a ▫₁ d) ▫₂ (b ▫₁ d)) 🝖-end

  moveₗ-to-invOp : let _ = op₂ , inverOpₗ in ∀{a b c} → (a ▫₁ b ≡ c) → (b ≡ a ▫₂ c)
  moveₗ-to-invOp {a = a} {b} {c} abc =
    b             🝖[ _≡_ ]-[ inverseOperₗ(_▫₁_)(_▫₂_) ]-sym
    a ▫₂ (a ▫₁ b) 🝖[ _≡_ ]-[ congruence₂-₂(_▫₂_)(a) abc ]
    a ▫₂ c        🝖-end

  moveᵣ-to-invOp : let _ = op₂ , inverOpᵣ in ∀{a b c} → (a ▫₁ b ≡ c) → (a ≡ c ▫₂ b)
  moveᵣ-to-invOp {a = a} {b} {c} abc =
    a             🝖[ _≡_ ]-[ inverseOperᵣ(_▫₁_)(_▫₂_) ]-sym
    (a ▫₁ b) ▫₂ b 🝖[ _≡_ ]-[ congruence₂-₁(_▫₂_)(b) abc ]
    c ▫₂ b        🝖-end
