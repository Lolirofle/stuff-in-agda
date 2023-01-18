module Formalization.Monoid where

import      Lvl
open import Numeral.Finite using (𝕟)
open import Numeral.Natural using (ℕ)
open import Type
open import Type.Dependent.Sigma
open import Syntax.Function

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}
private variable n n₁ n₂ : ℕ

module Monoid where
  open import Data.List
  open import Data.List.Functions

  -- A term in the language of a monoid.
  -- It consists of a finite number of variables, an identity element, and a binary operator on its elements.
  data Term (n : ℕ) : Type{Lvl.𝟎} where
    var : 𝕟(n) → Term(n)
    _▫_ : Term(n) → Term(n) → Term(n)
    id : Term(n)

  -- A fully normalised term in the language of a monoid is always able to be represented as a list of variables.
  -- See `normalize` for how a term is represented as a list.
  NormalForm : ℕ → Type
  NormalForm(n) = List(𝕟(n))

  -- Normalizes a term to its normal form.
  normalize : Term(n) → NormalForm(n)
  normalize (var v) = singleton v
  normalize (x ▫ y) = normalize x ++ normalize y
  normalize id      = ∅

  open import Structure.Function
  open import Structure.Function.Multi
  open import Structure.Operator
  open import Structure.Operator.Monoid
  open import Structure.Operator.Properties
  open import Structure.Relator.Properties
  open import Structure.Setoid
  open import Syntax.Transitivity

  module Semantics ⦃ equiv : Equiv{ℓₑ}(T) ⦄ (_∙_ : T → T → T) ⦃ monoid : Monoid(_∙_) ⦄ where
    open Structure.Operator.Monoid.Monoid(monoid) using () renaming (id to 𝑒)

    -- The environment for evaluating an expression is just a mapping from its variables to the values.
    Env : ℕ → Type
    Env(n) = (𝕟(n) → T)

    -- The semantics of the terms.
    eval : Env(n) → Term(n) → T
    eval env (var n) = env n
    eval env (x ▫ y) = eval env x ∙ eval env y
    eval env id      = 𝑒

    -- The semantics of the normal form.
    evalNormal : Env(n) → NormalForm(n) → T
    evalNormal env ∅       = 𝑒
    evalNormal env (v ⊰ l) = env v ∙ evalNormal env l

    module Proofs where
      private variable env : Env(n)
      private variable e : Term(n)

      instance
        eval-preserves : Preserving₂(eval env)(_▫_)(_∙_)
        eval-preserves = intro(reflexivity(_≡_))

      instance
        evalNormal-preserves : Preserving₂(evalNormal env)(_++_)(_∙_)
        evalNormal-preserves {env = env} = intro(\{x y} → proof{x}{y}) where
          proof : Names.Preserving₂(evalNormal env)(_++_)(_∙_)
          proof {∅}      {ys} = symmetry(_≡_) (identityₗ(_∙_)(𝑒))
          proof {x ⊰ xs} {ys} =
            evalNormal env ((x ⊰ xs) ++ ys)                 🝖[ _≡_ ]-[]
            evalNormal env (x ⊰ (xs ++ ys))                 🝖[ _≡_ ]-[]
            env x ∙ evalNormal env (xs ++ ys)               🝖[ _≡_ ]-[ congruence₂-₂(_∙_)(_) (proof {xs}{ys}) ]
            env x ∙ (evalNormal env xs ∙ evalNormal env ys) 🝖[ _≡_ ]-[ associativity(_∙_) ]-sym
            (env x ∙ evalNormal env xs) ∙ evalNormal env ys 🝖[ _≡_ ]-[]
            evalNormal env (x ⊰ xs) ∙ evalNormal env ys     🝖-end

      normalize-eval-correctness : (evalNormal env (normalize e) ≡ eval env e)
      normalize-eval-correctness {env = env} {var v} = identityᵣ(_∙_)(𝑒)
      normalize-eval-correctness {env = env} {x ▫ y} =
        evalNormal env (normalize (x ▫ y))                          🝖[ _≡_ ]-[]
        evalNormal env (normalize x ++ normalize y)                 🝖[ _≡_ ]-[ preserving₂(evalNormal env)(_++_)(_∙_) {normalize x}{normalize y} ]
        evalNormal env (normalize x) ∙ evalNormal env (normalize y) 🝖[ _≡_ ]-[ congruence₂(_∙_) (normalize-eval-correctness{env = env}{x}) (normalize-eval-correctness{env = env}{y}) ]
        eval env x ∙ eval env y                                     🝖[ _≡_ ]-[]
        eval env (x ▫ y)                                            🝖-end
      normalize-eval-correctness {env = env} {id}    = reflexivity(_≡_)

module CommutativeMonoid where

module CommutativeRig where
  open import Data.ListSized
  open import Formalization.Polynomial as Polynomial using (Polynomial)

  -- A term in the language of a commutative rig.
  -- It consists of a finite number of variables and a binary operator on its elements.
  data Term (n : ℕ) : Type{Lvl.𝟎} where
    var : 𝕟(n) → Term(n)
    _➕_ : Term(n) → Term(n) → Term(n)
    _✖_ : Term(n) → Term(n) → Term(n)
    𝟎 : Term(n)
    𝟏 : Term(n)

  NormalForm : ℕ → Type
  NormalForm = Polynomial

  {-
  normalize : Term(n) → NormalForm(n)
  normalize (var x) = {!!}
  normalize (t ➕ t₁) = {!!}
  normalize (t ✖ t₁) = {!!}
  normalize 𝟎 = {!!}
  normalize 𝟏 = {!!}
  -}
