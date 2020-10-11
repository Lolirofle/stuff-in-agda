module Structure.Operator.Proofs.Util where

import Lvl
open import Data
open import Data.Tuple
open import Functional hiding (id)
open import Function.Equals
import      Function.Names as Names
open import Logic.Predicate
open import Structure.Setoid.WithLvl
open import Structure.Function.Domain
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

module One {ℓ ℓₑ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {_▫_ : T → T → T} where
  private variable {id idₗ idᵣ ab abₗ abᵣ} : T
  private variable {inv invₗ invᵣ} : T → T
  private variable ⦃ op ⦄ : BinaryOperator ⦃ equiv ⦄ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫_)
  private variable ⦃ comm ⦄ : Commutativity ⦃ equiv ⦄ (_▫_)
  private variable ⦃ cancₗ ⦄ : Cancellationₗ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫_)
  private variable ⦃ cancᵣ ⦄ : Cancellationᵣ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫_)
  private variable ⦃ assoc ⦄ : Associativity ⦃ equiv ⦄ (_▫_)
  private variable ⦃ ident  ⦄ : Identity ⦃ equiv ⦄ (_▫_)(id)
  private variable ⦃ identₗ ⦄ : Identityₗ ⦃ equiv ⦄ (_▫_)(id)
  private variable ⦃ identᵣ ⦄ : Identityᵣ ⦃ equiv ⦄ (_▫_)(id)
  private variable ⦃ inver  ⦄ : InverseFunction ⦃ equiv ⦄ (_▫_) ⦃ [∃]-intro(id) ⦃ ident ⦄ ⦄ (inv)
  private variable ⦃ inverₗ ⦄ : InverseFunctionₗ ⦃ equiv ⦄ (_▫_) ⦃ [∃]-intro(idₗ) ⦃ identₗ ⦄ ⦄ (invₗ)
  private variable ⦃ inverᵣ ⦄ : InverseFunctionᵣ ⦃ equiv ⦄ (_▫_) ⦃ [∃]-intro(idᵣ) ⦃ identᵣ ⦄ ⦄ (invᵣ)
  private variable ⦃ inverPropₗ ⦄ : InversePropertyₗ ⦃ equiv ⦄ (_▫_) (invₗ)
  private variable ⦃ inverPropᵣ ⦄ : InversePropertyᵣ ⦃ equiv ⦄ (_▫_) (invᵣ)
  private variable ⦃ invol ⦄ : Involution ⦃ equiv ⦄ (inv)
  private variable ⦃ absorb  ⦄ : Absorber ⦃ equiv ⦄ (_▫_)(ab)
  private variable ⦃ absorbₗ ⦄ : Absorberₗ ⦃ equiv ⦄ (_▫_)(ab)
  private variable ⦃ absorbᵣ ⦄ : Absorberᵣ ⦃ equiv ⦄ (_▫_)(ab)

  -- TODO: Rename this to associate-commute4-commuting
  associate-commute4 : let _ = op , assoc in ∀{a b c d} → Names.Commuting(_▫_)(b)(c) → ((a ▫ b) ▫ (c ▫ d) ≡ (a ▫ c) ▫ (b ▫ d))
  associate-commute4 {a}{b}{c}{d} com =
    (a ▫ b) ▫ (c ▫ d) 🝖-[ symmetry(_≡_) (associativity(_▫_) {a ▫ b} {c} {d}) ]
    ((a ▫ b) ▫ c) ▫ d 🝖-[ congruence₂ₗ(_▫_)(d) (associativity(_▫_) {a} {b} {c}) ]
    (a ▫ (b ▫ c)) ▫ d 🝖-[ (congruence₂ₗ(_▫_)(d) ∘ congruence₂ᵣ(_▫_)(a)) com ]
    (a ▫ (c ▫ b)) ▫ d 🝖-[ associativity(_▫_) {a} {c ▫ b} {d} ]
    a ▫ ((c ▫ b) ▫ d) 🝖-[ congruence₂ᵣ(_▫_)(a) (associativity(_▫_) {c} {b} {d}) ]
    a ▫ (c ▫ (b ▫ d)) 🝖-[ symmetry(_≡_) (associativity(_▫_) {a} {c} {b ▫ d}) ]
    (a ▫ c) ▫ (b ▫ d) 🝖-end

  -- TODO: Rename this to associate-commute4
  associate-commute4-c : let _ = op , assoc , comm in ∀{a b c d} → ((a ▫ b) ▫ (c ▫ d) ≡ (a ▫ c) ▫ (b ▫ d))
  associate-commute4-c = associate-commute4(commutativity(_▫_))

  associate4-123-321 : let _ = op , assoc in ∀{a b c d} → (((a ▫ b) ▫ c) ▫ d ≡ a ▫ (b ▫ (c ▫ d)))
  associate4-123-321 {a}{b}{c}{d} = associativity(_▫_) 🝖 associativity(_▫_)

  associate4-123-213 : let _ = op , assoc in ∀{a b c d} → (((a ▫ b) ▫ c) ▫ d ≡ (a ▫ (b ▫ c)) ▫ d)
  associate4-123-213 {a}{b}{c}{d} = congruence₂ₗ(_▫_)(_) (associativity(_▫_))

  associate4-321-231 : let _ = op , assoc in ∀{a b c d} → (a ▫ (b ▫ (c ▫ d)) ≡ a ▫ ((b ▫ c) ▫ d))
  associate4-321-231 {a}{b}{c}{d} = congruence₂ᵣ(_▫_)(_) (symmetry(_≡_) (associativity(_▫_)))

  associate4-231-222 : let _ = op , assoc in ∀{a b c d} → (a ▫ ((b ▫ c) ▫ d) ≡ (a ▫ b) ▫ (c ▫ d))
  associate4-231-222 {a}{b}{c}{d} = symmetry(_≡_) associate4-321-231 🝖 symmetry(_≡_) associate4-123-321 🝖 associativity(_▫_)

  commuteᵣ-assocₗ : let _ = op , assoc , comm in ∀{a b c} → (((a ▫ b) ▫ c) ≡ ((a ▫ c) ▫ b))
  commuteᵣ-assocₗ {a}{b}{c} =
    (a ▫ b) ▫ c 🝖-[ associativity(_▫_) ]
    a ▫ (b ▫ c) 🝖-[ congruence₂ᵣ(_▫_)(_) (commutativity(_▫_)) ]
    a ▫ (c ▫ b) 🝖-[ associativity(_▫_) ]-sym
    (a ▫ c) ▫ b 🝖-end

  commuteₗ-assocᵣ : let _ = op , assoc , comm in ∀{a b c} → ((a ▫ (b ▫ c)) ≡ (b ▫ (a ▫ c)))
  commuteₗ-assocᵣ {a}{b}{c} =
    a ▫ (b ▫ c) 🝖-[ associativity(_▫_) ]-sym
    (a ▫ b) ▫ c 🝖-[ congruence₂ₗ(_▫_)(_) (commutativity(_▫_)) ]
    (b ▫ a) ▫ c 🝖-[ associativity(_▫_) ]
    b ▫ (a ▫ c) 🝖-end

  commuteᵣ-assocᵣ : let _ = op , assoc , comm in ∀{a b c} → ((a ▫ (b ▫ c)) ≡ ((a ▫ c) ▫ b))
  commuteᵣ-assocᵣ = symmetry(_≡_) (associativity(_▫_)) 🝖 commuteᵣ-assocₗ

  -- TODO: Rename and generalize this (See commuteBoth in Structure.Operator.Properties)
  commuteBothTemp : let _ = comm in ∀{a₁ a₂ b₁ b₂} → (a₁ ▫ a₂ ≡ b₁ ▫ b₂) → (a₂ ▫ a₁ ≡ b₂ ▫ b₁)
  commuteBothTemp {a₁} {a₂} {b₁} {b₂} p =
    a₂ ▫ a₁ 🝖-[ commutativity(_▫_) ]-sym
    a₁ ▫ a₂ 🝖-[ p ]
    b₁ ▫ b₂ 🝖-[ commutativity(_▫_) ]
    b₂ ▫ b₁ 🝖-end

module OneTypeTwoOp {ℓ ℓₑ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {_▫₁_ _▫₂_ : T → T → T} where
  private variable {id} : T
  private variable {inv} : T → T

  private variable ⦃ op₁ ⦄ : BinaryOperator ⦃ equiv ⦄ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₁_)
  private variable ⦃ comm₁ ⦄ : Commutativity ⦃ equiv ⦄ (_▫₁_)
  private variable ⦃ cancₗ₁ ⦄ : Cancellationₗ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₁_)
  private variable ⦃ cancᵣ₁ ⦄ : Cancellationᵣ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₁_)
  private variable ⦃ assoc₁ ⦄ : Associativity ⦃ equiv ⦄ (_▫₁_)
  private variable ⦃ ident₁  ⦄ : Identity ⦃ equiv ⦄ (_▫₁_)(id)
  private variable ⦃ identₗ₁ ⦄ : Identityₗ ⦃ equiv ⦄ (_▫₁_)(id)
  private variable ⦃ identᵣ₁ ⦄ : Identityᵣ ⦃ equiv ⦄ (_▫₁_)(id)
  private variable ⦃ inver₁  ⦄ : InverseFunction ⦃ equiv ⦄ (_▫₁_) ⦃ [∃]-intro(id) ⦃ ident₁ ⦄ ⦄ (inv)
  private variable ⦃ inverₗ₁ ⦄ : InverseFunctionₗ ⦃ equiv ⦄ (_▫₁_) ⦃ [∃]-intro(id) ⦃ identₗ₁ ⦄ ⦄ (inv)
  private variable ⦃ inverᵣ₁ ⦄ : InverseFunctionᵣ ⦃ equiv ⦄ (_▫₁_) ⦃ [∃]-intro(id) ⦃ identᵣ₁ ⦄ ⦄ (inv)
  private variable ⦃ absorbₗ₁ ⦄ : Absorberₗ ⦃ equiv ⦄ (_▫₁_)(id)
  private variable ⦃ absorbᵣ₁ ⦄ : Absorberᵣ ⦃ equiv ⦄ (_▫₁_)(id)

  private variable ⦃ op₂ ⦄ : BinaryOperator ⦃ equiv ⦄ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₂_)
  private variable ⦃ comm₂ ⦄ : Commutativity ⦃ equiv ⦄ (_▫₂_)
  private variable ⦃ cancₗ₂ ⦄ : Cancellationₗ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₂_)
  private variable ⦃ cancᵣ₂ ⦄ : Cancellationᵣ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₂_)
  private variable ⦃ assoc₂ ⦄ : Associativity ⦃ equiv ⦄ (_▫₂_)
  private variable ⦃ ident₂  ⦄ : Identity ⦃ equiv ⦄ (_▫₂_)(id)
  private variable ⦃ identₗ₂ ⦄ : Identityₗ ⦃ equiv ⦄ (_▫₂_)(id)
  private variable ⦃ identᵣ₂ ⦄ : Identityᵣ ⦃ equiv ⦄ (_▫₂_)(id)
  private variable ⦃ inver₂  ⦄ : InverseFunction ⦃ equiv ⦄ (_▫₂_) ⦃ [∃]-intro(id) ⦃ ident₂ ⦄ ⦄ (inv)
  private variable ⦃ inverₗ₂ ⦄ : InverseFunctionₗ ⦃ equiv ⦄ (_▫₂_) ⦃ [∃]-intro(id) ⦃ identₗ₂ ⦄ ⦄ (inv)
  private variable ⦃ inverᵣ₂ ⦄ : InverseFunctionᵣ ⦃ equiv ⦄ (_▫₂_) ⦃ [∃]-intro(id) ⦃ identᵣ₂ ⦄ ⦄ (inv)
  private variable ⦃ absorbₗ₂ ⦄ : Absorberₗ ⦃ equiv ⦄ (_▫₂_)(id)
  private variable ⦃ absorbᵣ₂ ⦄ : Absorberᵣ ⦃ equiv ⦄ (_▫₂_)(id)

  private variable ⦃ distriₗ ⦄ : Distributivityₗ ⦃ equiv ⦄ (_▫₁_)(_▫₂_)
  private variable ⦃ distriᵣ ⦄ : Distributivityᵣ ⦃ equiv ⦄ (_▫₁_)(_▫₂_)
  private variable ⦃ absorpₗ ⦄ : Absorptionₗ ⦃ equiv ⦄ (_▫₁_)(_▫₂_)
  private variable ⦃ absorpᵣ ⦄ : Absorptionᵣ ⦃ equiv ⦄ (_▫₁_)(_▫₂_)

  cross-distribute : let _ = op₂ , distriₗ , distriᵣ in ∀{a b c d} → (a ▫₂ b) ▫₁ (c ▫₂ d) ≡ ((a ▫₁ c) ▫₂ (b ▫₁ c)) ▫₂ ((a ▫₁ d) ▫₂ (b ▫₁ d))
  cross-distribute {a = a}{b}{c}{d} =
    (a ▫₂ b) ▫₁ (c ▫₂ d)                             🝖-[ distributivityₗ(_▫₁_)(_▫₂_) ]
    ((a ▫₂ b) ▫₁ c) ▫₂ ((a ▫₂ b) ▫₁ d)               🝖-[ congruence₂(_▫₂_) (distributivityᵣ(_▫₁_)(_▫₂_)) (distributivityᵣ(_▫₁_)(_▫₂_)) ]
    ((a ▫₁ c) ▫₂ (b ▫₁ c)) ▫₂ ((a ▫₁ d) ▫₂ (b ▫₁ d)) 🝖-end
