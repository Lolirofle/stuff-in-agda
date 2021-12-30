open import Type

module Formalization.ClassicalPropositionalLogic.TruthTable {ℓₚ}{P : Type{ℓₚ}} where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Operators using () renaming (module Logic to Bool)
import      Data.Boolean.Proofs as Bool
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Logic
open import Data.Either as Either using (_‖_ ; Left ; Right)
open import Data.Tuple as Tuple using ()
open import Formalization.ClassicalPropositionalLogic.Syntax
open import Formalization.ClassicalPropositionalLogic.Semantics
open import Functional
import      Logic.Propositional as Logic
open import Logic.Propositional.Equiv
import      Logic.Propositional.Theorems as Logic
open import Logic
open import Relator.Equals.Proofs.Equiv
import      Sets.PredicateSet
open        Sets.PredicateSet.BoundedQuantifiers
open import Structure.Relator

private variable ℓ : Lvl.Level

-- `_⊧_`, but decidable.
eval : Model(P) → Formula(P) → Bool
eval env (• p)   = env(p)
eval env (⊤)     = 𝑇
eval env (⊥)     = 𝐹
eval env (¬ φ)   = Bool.¬(eval env (φ))
eval env (φ ∧ ψ) = eval env (φ) Bool.∧ eval env (ψ)
eval env (φ ∨ ψ) = eval env (φ) Bool.∨ eval env (ψ)
eval env (φ ⟶ ψ) = eval env (φ) Bool.⟶ eval env (ψ)
eval env (φ ⟷ ψ) = eval env (φ) Bool.⟷ eval env (ψ)

_⊢_ : Formulas(P){ℓ} → Formula(P) → Stmt
Γ ⊢ φ = ∀{𝔐} → (∀ₛ(Γ) (IsTrue ∘ eval 𝔐)) → IsTrue(eval 𝔐 φ)

private variable Γ Γ₁ Γ₂ : Formulas(P){ℓ}
private variable φ ψ : Formula(P)
private variable 𝔐 : Model(P)

models-to-eval : (𝔐 ⊧ φ) → IsTrue(eval 𝔐 φ)
eval-to-models : IsTrue(eval 𝔐 φ) → (𝔐 ⊧ φ)

eval-to-models {φ = • x}   p = p
eval-to-models {φ = ⊤}     p = <>
eval-to-models {φ = ⊥}     p = p
eval-to-models {φ = ¬ φ}   p = Logic.[↔]-to-[→] IsTrue.preserves-[!][¬] p ∘ models-to-eval {φ = φ}
eval-to-models {φ = φ ∧ ψ} p = Tuple.map (eval-to-models {φ = φ}) (eval-to-models {φ = ψ}) (Logic.[↔]-to-[→] IsTrue.preserves-[&&][∧] p)
eval-to-models {φ = φ ∨ ψ} p = Either.map (eval-to-models {φ = φ}) (eval-to-models {φ = ψ}) (Logic.[↔]-to-[→] IsTrue.preserves-[||][∨] p)
eval-to-models {φ = φ ⟶ ψ} p = Either.map (Logic.contrapositiveᵣ (models-to-eval {φ = φ}) ∘ Logic.[↔]-to-[→] IsTrue.preserves-[!][¬]) (eval-to-models {φ = ψ}) (Logic.[↔]-to-[→] IsTrue.preserves-[||][∨] (substitute₁ᵣ(IsTrue) Bool.[→?]-disjunctive-form p))
eval-to-models {φ = φ ⟷ ψ} p = Either.map (Tuple.map (eval-to-models {φ = φ}) (eval-to-models {φ = ψ}) ∘ (Logic.[↔]-to-[→] IsTrue.preserves-[&&][∧])) (Tuple.map (Logic.contrapositiveᵣ (models-to-eval {φ = φ}) ∘ Logic.[↔]-to-[→] IsTrue.preserves-[!][¬]) (Logic.contrapositiveᵣ (models-to-eval {φ = ψ}) ∘ Logic.[↔]-to-[→] IsTrue.preserves-[!][¬]) ∘ Logic.[↔]-to-[→] IsTrue.preserves-[&&][∧]) (Logic.[↔]-to-[→] IsTrue.preserves-[||][∨] (substitute₁ᵣ(IsTrue) Bool.[==]-disjunctive-form p))

models-to-eval {φ = • x}   p = p
models-to-eval {φ = ⊤}     p = <>
models-to-eval {φ = ⊥}     p = p
models-to-eval {φ = ¬ φ}   p = Logic.[↔]-to-[←] IsTrue.preserves-[!][¬] (p ∘ eval-to-models {φ = φ})
models-to-eval {φ = φ ∧ ψ} p = Logic.[↔]-to-[←] IsTrue.preserves-[&&][∧] (Tuple.map (models-to-eval {φ = φ}) (models-to-eval {φ = ψ}) p)
models-to-eval {φ = φ ∨ ψ} p = Logic.[↔]-to-[←] IsTrue.preserves-[||][∨] (Either.map (models-to-eval {φ = φ}) (models-to-eval {φ = ψ}) p)
models-to-eval {φ = φ ⟶ ψ} p = substitute₁ₗ(IsTrue) Bool.[→?]-disjunctive-form (Logic.[↔]-to-[←] IsTrue.preserves-[||][∨] (Either.map (Logic.[↔]-to-[←] IsTrue.preserves-[!][¬] ∘ Logic.contrapositiveᵣ (eval-to-models {φ = φ})) (models-to-eval {φ = ψ}) p))
models-to-eval {φ = φ ⟷ ψ} p = substitute₁ₗ(IsTrue) Bool.[==]-disjunctive-form (Logic.[↔]-to-[←] IsTrue.preserves-[||][∨] (Either.map (Logic.[↔]-to-[←] IsTrue.preserves-[&&][∧] ∘ Tuple.map (models-to-eval {φ = φ}) (models-to-eval {φ = ψ})) (Logic.[↔]-to-[←] IsTrue.preserves-[&&][∧] ∘ Tuple.map (Logic.[↔]-to-[←] IsTrue.preserves-[!][¬] ∘ Logic.contrapositiveᵣ (eval-to-models {φ = φ})) (Logic.[↔]-to-[←] IsTrue.preserves-[!][¬] ∘ Logic.contrapositiveᵣ (eval-to-models {φ = ψ}))) p))

completeness : (Γ ⊨ φ) → (Γ ⊢ φ)
completeness {φ = φ} Γφ {𝔐} a = models-to-eval {φ = φ} (Γφ (\{γ} → eval-to-models {φ = γ} ∘ a))

soundness : (Γ ⊢ φ) → (Γ ⊨ φ)
soundness {φ = φ} Γφ {𝔐} a = eval-to-models {φ = φ} (Γφ (\{γ} → models-to-eval {φ = γ} ∘ a))
