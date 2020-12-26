module Structure.Groupoid.Groupoids where

open import Data
open import Data.Proofs
open import Functional
open import Logic
import      Lvl
import      Relator.Equals as Eq
open import Structure.Setoid
open import Structure.Groupoid
open import Structure.Categorical.Proofs
open import Structure.Categorical.Properties
open import Structure.Operator
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ : Lvl.Level
private variable Obj A B : Type{ℓ}
private variable _▫_ : Obj → Obj → Type{ℓ}
private variable f : A → B

emptyGroupoid : Groupoid{ℓ₁}{ℓ₂}{ℓₑ}(empty-morphism) ⦃ \{} ⦄
Groupoid._∘_            emptyGroupoid = empty-comp
Groupoid.id             emptyGroupoid = empty-id
Groupoid.inv            emptyGroupoid = empty-inv
Groupoid.binaryOperator emptyGroupoid {}
Groupoid.associativity  emptyGroupoid = empty-associativity ⦃ \{} ⦄
Groupoid.identity       emptyGroupoid = empty-identity ⦃ \{} ⦄
Groupoid.inverter       emptyGroupoid = empty-inverter ⦃ \{} ⦄

singleGroupoid : ∀{ℓₒ ℓᵢ ℓₚₐ₁ ℓₚₐ₂ ℓₚᵢ₁ ℓₚᵢ₂ ℓₚᵢ₃ ℓᵢₙ : Lvl.Level} → Groupoid{ℓ₁}{ℓ₂}(single-morphism)
Groupoid._∘_ (singleGroupoid{ℓ₁}{ℓ₂}{ℓₒ}{ℓᵢ}{ℓₚₐ₁}{ℓₚₐ₂}{ℓₚᵢ₁}{ℓₚᵢ₂}{ℓₚᵢ₃}) = single-comp{ℓ₂}{ℓₒ}
Groupoid.id  (singleGroupoid{ℓ₁}{ℓ₂}{ℓₒ}{ℓᵢ}{ℓₚₐ₁}{ℓₚₐ₂}{ℓₚᵢ₁}{ℓₚᵢ₂}{ℓₚᵢ₃}) = single-id{ℓ₂}{ℓᵢ}
Groupoid.inv (singleGroupoid{ℓ₁}{ℓ₂}{ℓₒ}{ℓᵢ}{ℓₚₐ₁}{ℓₚₐ₂}{ℓₚᵢ₁}{ℓₚᵢ₂}{ℓₚᵢ₃}) = single-inv{ℓ₂}{ℓᵢ}
BinaryOperator.congruence (Groupoid.binaryOperator singleGroupoid) Eq.[≡]-intro Eq.[≡]-intro = Eq.[≡]-intro
Groupoid.associativity (singleGroupoid{ℓ₁}{ℓ₂}{ℓₒ}{ℓᵢ}{ℓₚₐ₁}{ℓₚₐ₂}{ℓₚᵢ₁}{ℓₚᵢ₂}{ℓₚᵢ₃}) = single-associativity{ℓ₂}{ℓ₂}{ℓₚₐ₁}{ℓ₁}{ℓₚₐ₂}
Groupoid.identity      (singleGroupoid{ℓ₁}{ℓ₂}{ℓₒ}{ℓᵢ}{ℓₚₐ₁}{ℓₚₐ₂}{ℓₚᵢ₁}{ℓₚᵢ₂}{ℓₚᵢ₃}) = single-identity{ℓ₂}{ℓ₂}{ℓₚᵢ₁}{ℓ₁}{ℓₚᵢ₂}{ℓₚᵢ₃}
Groupoid.inverter      (singleGroupoid{ℓ₁}{ℓ₂}{ℓₒ}{ℓᵢ}{ℓₚₐ₁}{ℓₚₐ₂}{ℓₚᵢ₁}{ℓₚᵢ₂}{ℓₚᵢ₃}{ℓᵢₙ}) = single-inverter{ℓ₂}{ℓ₂}{ℓₚᵢ₁}{ℓ₁}{ℓₚᵢ₂}{ℓₚᵢ₃}{ℓᵢₙ}

on₂-groupoid : ⦃ morphism-equiv : ∀{x y} → Equiv{ℓₑ}{ℓ}(x ▫ y) ⦄ → Groupoid{Obj = B}(_▫_) ⦃ morphism-equiv ⦄ → (f : A → B) → Groupoid((_▫_) on₂ f)
Groupoid._∘_ (on₂-groupoid C _) = Groupoid._∘_ C
Groupoid.id  (on₂-groupoid C _) = Groupoid.id  C
Groupoid.inv (on₂-groupoid C _) = Groupoid.inv C
BinaryOperator.congruence (Groupoid.binaryOperator (on₂-groupoid C _)) = BinaryOperator.congruence(Groupoid.binaryOperator C)
Groupoid.associativity (on₂-groupoid C f) = on₂-associativity f (Groupoid.associativity C)
Groupoid.identity      (on₂-groupoid C f) = on₂-identity f (Groupoid.identity C)
Groupoid.inverter      (on₂-groupoid C f) = on₂-inverter f (Groupoid.inverter C)
