open import Numeral.Natural
open import Relator.Equals
open import Type.Properties.Decidable
open import Type

module Formalization.ClassicalPredicateLogic.Syntax.Substitution
  {ℓₚ ℓᵥ ℓₒ}
  (Prop : ℕ → Type{ℓₚ})
  (Var : Type{ℓᵥ}) ⦃ var-eq-dec : Decidable(2)(_≡_ {T = Var}) ⦄
  (Obj : ℕ → Type{ℓₒ})
  where

open import Data.Boolean
open import Data.ListSized
import      Data.ListSized.Functions as List
open import Formalization.ClassicalPredicateLogic.Syntax(Prop)(Var)(Obj)

private variable n : ℕ

substituteTerm : Var → Term → Term → Term
substituteTerm₊ : Var → Term → List(Term)(n) → List(Term)(n)
substituteTerm v t (var x)    = if(decide(2)(_≡_) v x) then t else (var x)
substituteTerm v t (func f x) = func f (substituteTerm₊ v t x)
substituteTerm₊ {0}    v t ∅        = ∅
substituteTerm₊ {𝐒(n)} v t (x ⊰ xs) = (substituteTerm v t x ⊰ substituteTerm₊ {n} v t xs)

substitute : Var → Term → Formula → Formula
substitute v t (f $ x)  = f $ List.map (substituteTerm v t) x 
substitute v t ⊤        = ⊤
substitute v t ⊥        = ⊥
substitute v t (φ ∧ ψ)  = (substitute v t φ) ∧ (substitute v t ψ)
substitute v t (φ ∨ ψ)  = (substitute v t φ) ∨ (substitute v t ψ)
substitute v t (φ ⟶ ψ)  = (substitute v t φ) ⟶ (substitute v t ψ)
substitute v t (Ɐ(x) φ) = Ɐ(x) (if(decide(2)(_≡_) v x) then φ else (substitute v t φ))
substitute v t (∃(x) φ) = ∃(x) (if(decide(2)(_≡_) v x) then φ else (substitute v t φ))
