module Formalization.Semigroup where

open import Data.ListNonEmpty as List using (List₊ ; _++_ ; ∅ ; _⊰_)
import      Lvl
open import Numeral.Finite using (𝕟)
open import Numeral.Natural using (ℕ)
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}
private variable n n₁ n₂ : ℕ

-- A term in the language of a semigroup.
-- It consists of a finite number of variables and a binary operator on its elements.
data Term (n : ℕ) : Type{Lvl.𝟎} where
  var : 𝕟(n) → Term(n)
  _▫_ : Term(n) → Term(n) → Term(n)

-- A fully normalised term in the language of a monoid is always able to be represented as a list of variables.
-- See `normalize` for how a term is represented as a list.
NormalForm : ℕ → Type
NormalForm(n) = List₊(𝕟(n))

-- Normalizes a term to its normal form.
normalize : Term(n) → NormalForm(n)
normalize (var v) = List.singleton v
normalize (x ▫ y) = normalize x ++ normalize y

open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Setoid

module Semantics ⦃ equiv : Equiv{ℓₑ}(T) ⦄ (_∙_ : T → T → T) ⦃ oper : BinaryOperator(_∙_) ⦄ ⦃ assoc : Associativity(_∙_) ⦄ where
  -- The environment for evaluating an expression is just a mapping from its variables to the values.
  Env : ℕ → Type
  Env(n) = (𝕟(n) → T)

  -- The semantics of the terms.
  eval : Env(n) → Term(n) → T
  eval env (var n) = env n
  eval env (x ▫ y) = eval env x ∙ eval env y

  -- The semantics of the normal form.
  evalNormal : Env(n) → NormalForm(n) → T
  evalNormal env (List.singleton v) = env v
  evalNormal env (v ⊰ l@(_ ⊰ _))    = env v ∙ evalNormal env l

  module Proofs where
    open import Structure.Function.Multi
    open import Structure.Relator.Properties
    open import Syntax.Transitivity

    private variable env : Env(n)
    private variable e : Term(n)

    evalNormal-step : ∀{x}{l} → (evalNormal env (x ⊰ l) ≡ env x ∙ evalNormal env l)
    evalNormal-step {l = List.singleton y} = reflexivity(_≡_)
    evalNormal-step {l = y ⊰ l@(_ ⊰ _)}    = reflexivity(_≡_)

    instance
      eval-preserves : Preserving₂(eval env)(_▫_)(_∙_)
      eval-preserves = intro(reflexivity(_≡_))

    instance
      evalNormal-preserves : Preserving₂(evalNormal env)(_++_)(_∙_)
      evalNormal-preserves {env = env} = intro(\{x y} → proof{x}{y}) where
        proof : Names.Preserving₂(evalNormal env)(_++_)(_∙_)
        proof {List.singleton x} {ys} = evalNormal-step{x = x}{ys}
        proof {x ⊰ xs@(_ ⊰ _)}   {ys} =
          evalNormal env ((x ⊰ xs) ++ ys)                 🝖[ _≡_ ]-[]
          evalNormal env (x ⊰ (xs ++ ys))                 🝖[ _≡_ ]-[ evalNormal-step{x = x}{l = xs ++ ys} ]
          env x ∙ evalNormal env (xs ++ ys)               🝖[ _≡_ ]-[ congruence₂-₂(_∙_)(_) (proof {xs}{ys}) ]
          env x ∙ (evalNormal env xs ∙ evalNormal env ys) 🝖[ _≡_ ]-[ associativity(_∙_) ]-sym
          (env x ∙ evalNormal env xs) ∙ evalNormal env ys 🝖[ _≡_ ]-[]
          evalNormal env (x ⊰ xs) ∙ evalNormal env ys     🝖-end

    normalize-eval-correctness : (evalNormal env (normalize e) ≡ eval env e)
    normalize-eval-correctness {env = env} {var v} = reflexivity(_≡_)
    normalize-eval-correctness {env = env} {x ▫ y} =
      evalNormal env (normalize (x ▫ y))                          🝖[ _≡_ ]-[]
      evalNormal env (normalize x ++ normalize y)                 🝖[ _≡_ ]-[ preserving₂(evalNormal env)(_++_)(_∙_) {normalize x}{normalize y} ]
      evalNormal env (normalize x) ∙ evalNormal env (normalize y) 🝖[ _≡_ ]-[ congruence₂(_∙_) (normalize-eval-correctness{env = env}{x}) (normalize-eval-correctness{env = env}{y}) ]
      eval env x ∙ eval env y                                     🝖[ _≡_ ]-[]
      eval env (x ▫ y)                                            🝖-end
