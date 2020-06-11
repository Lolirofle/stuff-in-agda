module Numeral.Matrix.Proofs where

import      Lvl
open import Syntax.Number
open import Data
open import Data.Boolean
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
import      Functional as Fn
open import Function.Equals
open import Logic.Predicate
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Finite.Oper
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Matrix as Matrix using (Matrix)
open import Numeral.Natural
open import Numeral.CoordinateVector as Vector using (Vector)
open import Structure.Function
open import Structure.Operator.Group
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid.WithLvl
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T A B : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  private variable s : ℕ ⨯ ℕ
  private variable x y z id id₁ id₂ : T
  private variable f g inv : T → T
  private variable _▫_ _▫₁_ _▫₂_ : T → T → T

  instance
    matrix-equiv : Equiv(Matrix(s)(T))
    Equiv._≡_ matrix-equiv (Matrix.mat proj₁) (Matrix.mat proj₂) = proj₁ ⊜ proj₂
    Reflexivity.proof  (Equivalence.reflexivity  (Equiv.equivalence matrix-equiv)) = reflexivity(_⊜_)
    Symmetry.proof     (Equivalence.symmetry     (Equiv.equivalence matrix-equiv)) = symmetry(_⊜_)
    Transitivity.proof (Equivalence.transitivity (Equiv.equivalence matrix-equiv)) = transitivity(_⊜_)

  instance
    matrix-map₂-binaryOperator : ⦃ oper : BinaryOperator(_▫_) ⦄ → BinaryOperator(Matrix.map₂{s = s}(_▫_))
    BinaryOperator.congruence (matrix-map₂-binaryOperator {_▫_ = _▫_} ⦃ oper ⦄) (intro p) (intro q) = intro (congruence₂(_▫_) ⦃ oper ⦄ p q)

  instance
    matrix-map₂-identityₗ : ⦃ ident : Identityₗ(_▫_)(id) ⦄ → Identityₗ(Matrix.map₂{s = s}(_▫_)) (Matrix.fill(id))
    Identityₗ.proof (matrix-map₂-identityₗ {_▫_ = _▫_} {id = id}) = intro(identityₗ(_▫_)(id))

  instance
    matrix-map₂-identityᵣ : ⦃ ident : Identityᵣ(_▫_)(id) ⦄ → Identityᵣ(Matrix.map₂{s = s}(_▫_)) (Matrix.fill(id))
    Identityᵣ.proof (matrix-map₂-identityᵣ {_▫_ = _▫_} {id = id}) = intro(identityᵣ(_▫_)(id))

  instance
    matrix-map₂-identity : ⦃ ident : Identity(_▫_)(id) ⦄ → Identity(Matrix.map₂{s = s}(_▫_)) (Matrix.fill(id))
    matrix-map₂-identity = intro

  instance
    matrix-map₂-absorberₗ : ⦃ absorb : Absorberₗ(_▫_)(id) ⦄ → Absorberₗ(Matrix.map₂{s = s}(_▫_)) (Matrix.fill(id))
    Absorberₗ.proof (matrix-map₂-absorberₗ {_▫_ = _▫_} {id = id}) = intro(absorberₗ(_▫_)(id))

  instance
    matrix-map₂-absorberᵣ : ⦃ absorb : Absorberᵣ(_▫_)(id) ⦄ → Absorberᵣ(Matrix.map₂{s = s}(_▫_)) (Matrix.fill(id))
    Absorberᵣ.proof (matrix-map₂-absorberᵣ {_▫_ = _▫_} {id = id}) = intro(absorberᵣ(_▫_)(id))

  instance
    matrix-map₂-absorber : ⦃ absorb : Absorber(_▫_)(id) ⦄ → Absorber(Matrix.map₂{s = s}(_▫_)) (Matrix.fill(id))
    matrix-map₂-absorber = intro

  instance
    matrix-map₂-commutativity : ⦃ comm : Commutativity(_▫_) ⦄ → Commutativity(Matrix.map₂{s = s}(_▫_))
    Commutativity.proof (matrix-map₂-commutativity {_▫_ = _▫_}) = intro(commutativity(_▫_))

  instance
    matrix-map₂-associativity : ⦃ assoc : Associativity(_▫_) ⦄ → Associativity(Matrix.map₂{s = s}(_▫_))
    Associativity.proof (matrix-map₂-associativity {_▫_ = _▫_}) = intro(associativity(_▫_))

  instance
    matrix-map₂-map-inverseFunctionₗ : ⦃ ident : Identityₗ(_▫_)(id) ⦄ ⦃ inver : InverseFunctionₗ(_▫_) ⦃ [∃]-intro _ ⦄ (inv) ⦄ → InverseFunctionₗ(Matrix.map₂{s = s}(_▫_)) ⦃ [∃]-intro _ ⦄ (Matrix.map inv)
    InverseFunctionₗ.proof (matrix-map₂-map-inverseFunctionₗ {_▫_ = _▫_} {inv = inv}) = intro (inverseFunctionₗ(_▫_) ⦃ [∃]-intro _ ⦄ (inv))

  instance
    matrix-map₂-map-inverseFunctionᵣ : ⦃ ident : Identityᵣ(_▫_)(id) ⦄ ⦃ inver : InverseFunctionᵣ(_▫_) ⦃ [∃]-intro _ ⦄ (inv) ⦄ → InverseFunctionᵣ(Matrix.map₂{s = s}(_▫_)) ⦃ [∃]-intro _ ⦄ (Matrix.map inv)
    InverseFunctionᵣ.proof (matrix-map₂-map-inverseFunctionᵣ {_▫_ = _▫_} {inv = inv}) = intro (inverseFunctionᵣ(_▫_) ⦃ [∃]-intro _ ⦄ (inv))

  instance
    matrix-map₂-map-inverseFunction : ⦃ ident : Identity(_▫_)(id) ⦄ ⦃ inver : InverseFunction(_▫_) ⦃ [∃]-intro _ ⦄ (inv) ⦄ → InverseFunction(Matrix.map₂{s = s}(_▫_)) ⦃ [∃]-intro _ ⦄ (Matrix.map inv)
    matrix-map₂-map-inverseFunction = intro

  instance
    matrix-map-function : ⦃ func : Function(f) ⦄ → Function(Matrix.map{s = s} (f))
    Function.congruence matrix-map-function (intro p) = intro(congruence₁ _ p)

  instance
    matrix-map₂-monoid : ⦃ monoid : Monoid(_▫_) ⦄ → Monoid(Matrix.map₂{s = s}(_▫_))
    Monoid.identity-existence matrix-map₂-monoid = [∃]-intro(Matrix.fill(_))

  instance
    matrix-map₂-group : ⦃ group : Group(_▫_) ⦄ → Group(Matrix.map₂{s = s}(_▫_))
    Group.monoid matrix-map₂-group = matrix-map₂-monoid
    Group.inverse-existence matrix-map₂-group = [∃]-intro _

  -- scalarMat-element-zero : (Matrix.proj (Matrix.SquareMatrix.scalarMat zero elem) (x , y) ≡ zero) → ((x ≡ y) ↔ (zero ≡ elem))
  -- scalarMat-element-zero = 

{-
  instance
    matrix-multPattern-identityᵣ : ⦃ ident₁ : Identityᵣ(_▫₁_)(id₁) ⦄ ⦃ ident₂ : Identityᵣ(_▫₂_)(id₂) ⦄ → Identityᵣ(Matrix.multPattern(_▫₂_)(_▫₁_) id₁) (Matrix.SquareMatrix.scalarMat id₂ id₁)
    Dependent._⊜_.proof (Identityᵣ.proof (matrix-multPattern-identityᵣ {_▫₁_} {id₁} {_▫₂_} {id₂}) {M}) {x , y} =
      Matrix.proj (Matrix.multPattern(_▫₂_)(_▫₁_) id₁ M (Matrix.SquareMatrix.scalarMat id₂ id₁)) (x , y) 🝖[ _≡_ ]-[]
      Vector.foldᵣ(_▫₂_) id₁ (Vector.map₂(_▫₁_) (λ x₂ → Matrix.proj M (x , y)) (λ y₁ → Matrix.proj (Matrix.SquareMatrix.scalarMat id₂ id₁) (x , y₁))) 🝖[ _≡_ ]-[ {!!} ]
      Matrix.proj M (x , y) 🝖-end

  instance
    matrix-map₂-distributivityᵣ : ⦃ dist : Distributivityᵣ(_▫₁_)(_▫₂_) ⦄ → Distributivityᵣ(Matrix.multPattern(_▫₂_)(_▫₁_) id) (Matrix.map₂{s = s}(_▫₂_))
    _⊜_.proof (Distributivityᵣ.proof (matrix-map₂-distributivityᵣ {_▫₁_} {_▫₂_} {id = id}) {a} {b} {c}) {x , y} =
      Matrix.proj(Matrix.multPattern(_▫₂_) (_▫₁_) id (Matrix.map₂(_▫₂_) a b) c) (x , y) 🝖[ _≡_ ]-[]
      Vector.foldᵣ(_▫₂_) id (Vector.map₂ (_▫₁_) (Matrix.row(Matrix.map₂(_▫₂_) a b)(y)) (Matrix.col(c)(x))) 🝖[ _≡_ ]-[]

      Vector.foldᵣ(_▫₂_) id (Vector.map₂(_▫₁_) (λ x₁ → (Matrix.proj a (x₁ , y)) ▫₂ (Matrix.proj b (x₁ , y))) (λ y₁ → Matrix.proj c (x , y₁))) 🝖[ _≡_ ]-[ {!!} ]
      (Vector.foldᵣ(_▫₂_) id (Vector.map₂ _▫₁_ (λ x₁ → Matrix.proj a (x₁ , y)) (λ y₁ → Matrix.proj c (x , y₁)))) ▫₂ (Vector.foldᵣ(_▫₂_) id (Vector.map₂(_▫₁_) (λ x₁ → Matrix.proj b (x₁ , y)) (λ y₁ → Matrix.proj c (x , y₁)))) 🝖[ _≡_ ]-[]

      (Vector.foldᵣ(_▫₂_) id (Vector.map₂ (_▫₁_) (Matrix.row(a)(y)) (Matrix.col(c)(x)))) ▫₂ (Vector.foldᵣ(_▫₂_) id (Vector.map₂ (_▫₁_) (Matrix.row(b)(y)) (Matrix.col(c)(x)))) 🝖[ _≡_ ]-[]
      Matrix.proj(Matrix.map₂(_▫₂_) (Matrix.multPattern(_▫₂_)(_▫₁_) id a c) (Matrix.multPattern(_▫₂_)(_▫₁_) id b c)) (x , y) 🝖-end
-}
