open import Type
open import Logic.Classical as Logic using (Classical)
open import Logic.Predicate as Logic using ()

module Formalization.ClassicalPropositionalLogic ⦃ classical : ∀{ℓ} → Logic.∀ₗ(Classical{ℓ}) ⦄ where

import      Lvl
open import Data
open import Data.Boolean
import      Data.Boolean.Operators
open import Data.Boolean.Stmt
open import Data.Either as Either using (_‖_ ; Left ; Right)
open import Data.Tuple as Tuple using ()
private module BoolOp = Data.Boolean.Operators.Logic
open import Functional
open import Function.Names using (_⊜_)
open import Logic
open import Logic.Propositional as Logic using (_←_)
open import Logic.Propositional.Theorems as Logic using ()
open import Logic.Predicate.Theorems as Logic using ()
open import Relator.Equals
open import Relator.Equals.Proofs
open import Relator.Equals.Proofs.Equiv
open import Sets.PredicateSet using (PredSet ; _∈_ ; _∉_ ; _∪_ ; _∪•_ ; _∖_ ; _⊆_ ; _⊇_ ; ∅ ; [≡]-to-[⊆] ; [≡]-to-[⊇]) renaming (•_ to singleton ; _≡_ to _≡ₛ_)
open        Sets.PredicateSet.BoundedQuantifiers
open import Structure.Relator.Properties
open import Syntax.Function
open import Type.Size.Countable

private variable ℓₚ ℓ ℓ₁ ℓ₂ : Lvl.Level

module _ (P : Type{ℓₚ}) where
  -- Formulas.
  -- Inductive definition of the grammatical elements of the language of propositional logic.
  -- Note: It is possible to reduce the number of formula variants to for example {•,¬,∨} or {•,¬,∧} (This is called propositional adequacy/functional completeness).
  data Formula : Type{ℓₚ} where
    •_ : P → Formula -- Propositional constants

    ⊤ : Formula -- Tautology (Top / True)
    ⊥ : Formula -- Contradiction (Bottom / False)

    ¬_ : Formula → Formula -- Negation (Not)

    _∧_ : Formula → Formula → Formula -- Conjunction (And)
    _∨_ : Formula → Formula → Formula -- Disjunction (Or)
    _⟶_ : Formula → Formula → Formula -- Implication
    _⟷_ : Formula → Formula → Formula -- Equivalence

  Formulas : Type{ℓₚ Lvl.⊔ Lvl.𝐒(ℓ)}
  Formulas{ℓ} = PredSet{ℓ}(Formula)

  infixl 1011 •_
  infixl 1010 ¬_
  infixl 1005 _∧_
  infixl 1004 _∨_
  infixl 1000 _⟷_ _⟶_

module _ {P : Type{ℓₚ}} where
  -- Double negation
  -- ¬¬_ : Formula(P) → Formula(P)
  -- ¬¬_ : (¬_) ∘ (¬_)

  -- Reverse implication
  _⟵_ : Formula(P) → Formula(P) → Formula(P)
  _⟵_ = swap(_⟶_)

  -- (Nor)
  _⊽_ : Formula(P) → Formula(P) → Formula(P)
  _⊽_ = (¬_) ∘₂ (_∨_)

  -- (Nand)
  _⊼_ : Formula(P) → Formula(P) → Formula(P)
  _⊼_ = (¬_) ∘₂ (_∧_)

  -- (Exclusive or / Xor)
  _⊻_ : Formula(P) → Formula(P) → Formula(P)
  _⊻_ = (¬_) ∘₂ (_⟷_)

  infixl 1000 _⟵_

  -- TODO: How would a proof of this look like?
  instance
    postulate Formula-is-countably-infinite : ⦃ _ : CountablyInfinite(P) ⦄ → CountablyInfinite(Formula(P))
  {-
  open import Type.WellOrdering
  Formula-W-bijectivity : Bijective(W{A = 𝕟(8)}())
  Formula-W-bijectivity = {!!
  -}

module Semantics where
  private variable P : Type{ℓₚ}

  -- Model.
  -- A model decides which propositional constants that are true or false.
  Model : Type{ℓₚ} → Type{ℓₚ}
  Model(P) = (P → Bool)

  -- Satisfication relation.
  -- (𝔐 ⊧ φ) means that the formula φ is satisfied in the model 𝔐.
  -- Or in other words: A formula is true in the model 𝔐.
  _⊧_ : Model(P) → Formula(P) → Stmt
  𝔐 ⊧ (• p)   = IsTrue(𝔐(p))   -- A model decides whether a propositional constant is satisifed.
  𝔐 ⊧ ⊤       = Logic.⊤        -- Any model satisfies top.
  𝔐 ⊧ ⊥       = Logic.⊥        -- No model satisfies bottom.
  𝔐 ⊧ (¬ φ)   = Logic.¬(𝔐 ⊧ φ) -- A model satisfies a negated proposition when it does not satisfy the proposition.
  𝔐 ⊧ (φ ∧ ψ) = (𝔐 ⊧ φ) Logic.∧ (𝔐 ⊧ ψ) -- A model satisfies a conjunction when it satisfies both of the propositions.
  𝔐 ⊧ (φ ∨ ψ) = (𝔐 ⊧ φ) Logic.∨ (𝔐 ⊧ ψ) -- A model satisfies a disjunction when it satisfies any one of the propositions.
  𝔐 ⊧ (φ ⟶ ψ) = Logic.¬(𝔐 ⊧ φ) Logic.∨ (𝔐 ⊧ ψ)
  𝔐 ⊧ (φ ⟷ ψ) = ((𝔐 ⊧ φ) Logic.∧ (𝔐 ⊧ ψ)) Logic.∨ (Logic.¬(𝔐 ⊧ φ) Logic.∧ Logic.¬(𝔐 ⊧ ψ))

  -- Satisfication of a set of formulas.
  -- This means that a model satisfies all formulas at the same time.
  _⊧₊_ : Model(P) → Formulas(P){ℓ} → Stmt
  𝔐 ⊧₊ Γ = ∀ₛ(Γ) (𝔐 ⊧_)

  -- Validity of a formula.
  -- A formula is valid when it is true independent of any model.
  Valid : Formula(P) → Stmt
  Valid(φ) = Logic.∀ₗ(_⊧ φ)

  -- Satisfiability of sets of formulas.
  -- A set of formulas is valid when there is a model that satisfies all of them at the same time.
  Satisfiable : Formulas(P){ℓ} → Stmt
  Satisfiable(Γ) = Logic.∃(_⊧₊ Γ)

  -- Unsatisfiability of sets of formulas.
  Unsatisfiable : Formulas(P){ℓ} → Stmt
  Unsatisfiable{ℓ} = Logic.¬_ ∘ Satisfiable{ℓ}

  -- Semantic entailment of a formula.
  -- A hypothetical statement. If a model would satisfy all formulas in Γ, then this same model satisifes the formula φ.
  _⊨_ : Formulas(P){ℓ} → Formula(P) → Stmt
  Γ ⊨ φ = ∀{𝔐} → (𝔐 ⊧₊ Γ) → (𝔐 ⊧ φ)

  _⊭_ : Formulas(P){ℓ} → Formula(P) → Stmt
  _⊭_ = Logic.¬_ ∘₂ _⊨_

  -- Axiomatization of a theory by a set of axioms.
  -- A set of axioms is a set of formulas.
  -- A theory is the closure of a set of axioms.
  -- An axiomatization is a subset of formulas of the theory which entails all formulas in the axiomatized theory.
  _axiomatizes_ : Formulas(P){ℓ₁} → Formulas(P){ℓ₂} → Stmt
  Γ₁ axiomatizes Γ₂ = ∀{φ} → (Γ₁ ⊨ φ) → Γ₂(φ)

  -- A set of formulas is closed when it includes all formulas that it entails.
  Closed : Formulas(P){ℓ} → Stmt
  Closed(Γ) = Γ axiomatizes Γ

  module Proofs where
    private variable 𝔐 : Model(P)
    private variable Γ Γ₁ Γ₂ : Formulas(P){ℓ}
    private variable φ ψ : Formula(P)

    [⊧₊]-antimonotone : (Γ₁ ⊆ Γ₂) → ((_⊧₊ Γ₁) ⊇ (_⊧₊ Γ₂))
    [⊧₊]-antimonotone Γ₁Γ₂ 𝔐Γ₂ Γ₁γ = 𝔐Γ₂ (Γ₁Γ₂ Γ₁γ)

    [⊧₊]-strengthen : (𝔐 ⊧₊ Γ₁) → (𝔐 ⊧₊ Γ₂) → (𝔐 ⊧₊ (Γ₁ ∪ Γ₂))
    [⊧₊]-strengthen 𝔐Γ₁ 𝔐Γ₂ Γ₁Γ₂γ = Logic.[∨]-elim 𝔐Γ₁ 𝔐Γ₂ Γ₁Γ₂γ

    [⊧₊]-of-[∪]ₗ : (𝔐 ⊧₊ (Γ₁ ∪ Γ₂)) → (𝔐 ⊧₊ Γ₁)
    [⊧₊]-of-[∪]ₗ 𝔐Γ₁Γ₂ 𝔐Γ₁ = 𝔐Γ₁Γ₂ (Left 𝔐Γ₁)

    [⊧₊]-of-[∪]ᵣ : (𝔐 ⊧₊ (Γ₁ ∪ Γ₂)) → (𝔐 ⊧₊ Γ₂)
    [⊧₊]-of-[∪]ᵣ 𝔐Γ₁Γ₂ 𝔐Γ₂ = 𝔐Γ₁Γ₂ (Right 𝔐Γ₂)

    [⊧]-to-[⊧₊] : (𝔐 ⊧ φ) Logic.↔ (𝔐 ⊧₊ singleton(φ))
    [⊧]-to-[⊧₊] = Logic.[↔]-intro (_$ [≡]-intro) (\𝔐φ φγ → [≡]-substitutionᵣ φγ 𝔐φ)

    [⊧]-contradiction : (𝔐 ⊧ φ) → (𝔐 ⊧ (¬ φ)) → (𝔐 ⊧ ⊥)
    [⊧]-contradiction = apply

    [⊧]-of-[¬¬] : (𝔐 ⊧ ¬(¬ φ)) → (𝔐 ⊧ φ)
    [⊧]-of-[¬¬] = Logic.[¬¬]-elim

    [⊨]-monotone : (Γ₁ ⊆ Γ₂) → ((Γ₁ ⊨_) ⊆ (Γ₂ ⊨_))
    [⊨]-monotone Γ₁Γ₂ Γ₁φ 𝔐Γ₂ = Γ₁φ (Γ₁γ ↦ 𝔐Γ₂ (Γ₁Γ₂ Γ₁γ))

    [⊨]-functionₗ : (Γ₁ ≡ₛ Γ₂) → ((Γ₁ ⊨_) ≡ₛ (Γ₂ ⊨_))
    [⊨]-functionₗ {Γ₁ = Γ₁}{Γ₂ = Γ₂} Γ₁Γ₂ {φ} = Logic.[↔]-intro ([⊨]-monotone{Γ₁ = Γ₂}{Γ₂ = Γ₁}(\{x} → [≡]-to-[⊇] (Γ₁Γ₂{x}) {x}){φ}) ([⊨]-monotone{Γ₁ = Γ₁}{Γ₂ = Γ₂}(\{x} → [≡]-to-[⊆] (Γ₁Γ₂{x}) {x}){φ})

    [⊨]-weaken : (Γ₁ ⊨ φ) → ((Γ₁ ∪ Γ₂) ⊨ φ)
    [⊨]-weaken Γ₁φ 𝔐Γ₁Γ₂ = Γ₁φ (Γ₁γ ↦ 𝔐Γ₁Γ₂ (Left Γ₁γ))

    [⊨]-validity : (∀{Γ : Formulas(P){ℓ}} → (Γ ⊨ φ)) Logic.↔ Valid(φ)
    [⊨]-validity = Logic.[↔]-intro (λ r → const r) (λ l → l{∅} empty)

    [⊨]-contradiction : (Γ ⊨ φ) → (Γ ⊨ (¬ φ)) → (Γ ⊨ ⊥)
    [⊨]-contradiction Γφ Γ¬φ 𝔐Γ = Γ¬φ 𝔐Γ (Γφ 𝔐Γ)

    [⊨]-entailment-unsatisfiability : (Γ ⊨ φ) Logic.↔ Unsatisfiable(Γ ∪ singleton(¬ φ))
    [⊨]-entailment-unsatisfiability {Γ = Γ}{φ = φ} = Logic.[↔]-intro l r where
      l : (Γ ⊨ φ) ← Unsatisfiable(Γ ∪ singleton(¬ φ))
      l r {𝔐} 𝔐Γ = [⊧]-of-[¬¬] {𝔐 = 𝔐}{φ = φ} (𝔐¬φ ↦ r (Logic.[∃]-intro 𝔐 ⦃ Logic.[∨]-elim 𝔐Γ (\{[≡]-intro → 𝔐¬φ}) ⦄))

      r : (Γ ⊨ φ) → Unsatisfiable(Γ ∪ singleton(¬ φ))
      r l (Logic.[∃]-intro 𝔐 ⦃ sat ⦄) = [⊧]-contradiction {φ = φ} 𝔐φ 𝔐¬φ where
        𝔐φ  = l([⊧₊]-of-[∪]ₗ {Γ₁ = Γ} sat)
        𝔐¬φ = Logic.[↔]-to-[←] [⊧]-to-[⊧₊] ([⊧₊]-of-[∪]ᵣ {Γ₁ = Γ} sat)

    [⊨][⟶]-intro : ((Γ ∪ singleton(φ)) ⊨ ψ) Logic.↔ (Γ ⊨ (φ ⟶ ψ))
    [⊨][⟶]-intro {Γ = Γ}{φ = φ}{ψ = ψ} = Logic.[↔]-intro l r where
      l : (Γ ⊨ (φ ⟶ ψ)) → ((Γ ∪ singleton(φ)) ⊨ ψ)
      l φψ {𝔐 = 𝔐} 𝔐Γφ = Logic.[∨]-elim (¬φ ↦ Logic.[⊥]-elim(¬φ 𝔐φ)) id (φψ 𝔐Γ) where
        𝔐Γ : 𝔐 ⊧₊ Γ
        𝔐Γ {γ} Γγ = 𝔐Γφ {γ} (Logic.[∨]-introₗ Γγ)

        𝔐φ : 𝔐 ⊧ φ
        𝔐φ = 𝔐Γφ {φ} (Logic.[∨]-introᵣ [≡]-intro)

      r : ((Γ ∪ singleton(φ)) ⊨ ψ) → (Γ ⊨ (φ ⟶ ψ))
      r Γφψ {𝔐 = 𝔐} 𝔐Γ with Logic.excluded-middle(𝔐 ⊧ φ)
      ... | Logic.[∨]-introₗ 𝔐φ  = Logic.[∨]-introᵣ (Γφψ(Logic.[∨]-elim 𝔐Γ \{[≡]-intro → 𝔐φ}))
      ... | Logic.[∨]-introᵣ ¬𝔐φ = Logic.[∨]-introₗ ¬𝔐φ

    [⊨]-unsatisfiability : (Γ ⊨ ⊥) Logic.↔ Unsatisfiable(Γ)
    [⊨]-unsatisfiability {Γ = Γ} = Logic.[↔]-intro l r where
      l : (Γ ⊨ ⊥) ← Unsatisfiable(Γ)
      l unsatΓ {𝔐} 𝔐Γ = unsatΓ (Logic.[∃]-intro 𝔐 ⦃ 𝔐Γ ⦄)

      r : (Γ ⊨ ⊥) → Unsatisfiable(Γ)
      r Γ⊥ (Logic.[∃]-intro 𝔐 ⦃ 𝔐Γ ⦄) = Γ⊥ 𝔐Γ

    [⊨][¬]-intro : ((Γ ∪ singleton(φ)) ⊨ ⊥) Logic.↔ (Γ ⊨ (¬ φ))
    [⊨][¬]-intro {Γ = Γ}{φ = φ} = Logic.[↔]-intro l r where
      l : ((Γ ∪ singleton(φ)) ⊨ ⊥) ← (Γ ⊨ (¬ φ))
      l Γ¬φ 𝔐Γφ = Γ¬φ (𝔐Γφ ∘ Left) (𝔐Γφ (Right [≡]-intro))

      r : ((Γ ∪ singleton(φ)) ⊨ ⊥) → (Γ ⊨ (¬ φ))
      r Γφ⊥ 𝔐Γ 𝔐φ = Γφ⊥ ([⊧₊]-strengthen {Γ₁ = Γ}{Γ₂ = singleton(φ)} 𝔐Γ (Logic.[↔]-to-[→] [⊧]-to-[⊧₊] 𝔐φ))

module TruthTable {P : Type{ℓₚ}} where
  -- `_⊧_`, but decidable.
  eval : Semantics.Model(P) → Formula(P) → Bool
  eval env (• p)   = env(p)
  eval env (⊤)     = 𝑇
  eval env (⊥)     = 𝐹
  eval env (¬ φ)   = BoolOp.¬(eval env (φ))
  eval env (φ ∧ ψ) = eval env (φ) BoolOp.∧ eval env (ψ)
  eval env (φ ∨ ψ) = eval env (φ) BoolOp.∨ eval env (ψ)
  eval env (φ ⟶ ψ) = eval env (φ) BoolOp.⟶ eval env (ψ)
  eval env (φ ⟷ ψ) = eval env (φ) BoolOp.⟷ eval env (ψ)

  _⊢_ : Formulas(P){ℓ} → Formula(P) → Stmt
  Γ ⊢ φ = ∀{𝔐} → (∀ₛ(Γ) (IsTrue ∘ eval 𝔐)) → IsTrue(eval 𝔐 φ)

  import      Data.Boolean.Proofs as Bool
  open import Data.Boolean.Stmt.Proofs

  open Semantics
  open Semantics.Proofs

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
  eval-to-models {φ = φ ∨ ψ} p = Either.map2 (eval-to-models {φ = φ}) (eval-to-models {φ = ψ}) (Logic.[↔]-to-[→] IsTrue.preserves-[||][∨] p)
  eval-to-models {φ = φ ⟶ ψ} p = Either.map2 (Logic.contrapositiveᵣ (models-to-eval {φ = φ}) ∘ Logic.[↔]-to-[→] IsTrue.preserves-[!][¬]) (eval-to-models {φ = ψ}) (Logic.[↔]-to-[→] IsTrue.preserves-[||][∨] ([≡]-substitutionᵣ Bool.[→?]-disjunctive-form {f = IsTrue} p))
  eval-to-models {φ = φ ⟷ ψ} p = Either.map2 (Tuple.map (eval-to-models {φ = φ}) (eval-to-models {φ = ψ}) ∘ (Logic.[↔]-to-[→] IsTrue.preserves-[&&][∧])) (Tuple.map (Logic.contrapositiveᵣ (models-to-eval {φ = φ}) ∘ Logic.[↔]-to-[→] IsTrue.preserves-[!][¬]) (Logic.contrapositiveᵣ (models-to-eval {φ = ψ}) ∘ Logic.[↔]-to-[→] IsTrue.preserves-[!][¬]) ∘ Logic.[↔]-to-[→] IsTrue.preserves-[&&][∧]) (Logic.[↔]-to-[→] IsTrue.preserves-[||][∨] ([≡]-substitutionᵣ Bool.[==]-disjunctive-form {f = IsTrue} p))

  models-to-eval {φ = • x}   p = p
  models-to-eval {φ = ⊤}     p = <>
  models-to-eval {φ = ⊥}     p = p
  models-to-eval {φ = ¬ φ}   p = Logic.[↔]-to-[←] IsTrue.preserves-[!][¬] (p ∘ eval-to-models {φ = φ})
  models-to-eval {φ = φ ∧ ψ} p = Logic.[↔]-to-[←] IsTrue.preserves-[&&][∧] (Tuple.map (models-to-eval {φ = φ}) (models-to-eval {φ = ψ}) p)
  models-to-eval {φ = φ ∨ ψ} p = Logic.[↔]-to-[←] IsTrue.preserves-[||][∨] (Either.map2 (models-to-eval {φ = φ}) (models-to-eval {φ = ψ}) p)
  models-to-eval {φ = φ ⟶ ψ} p = [≡]-substitutionₗ Bool.[→?]-disjunctive-form {f = IsTrue} (Logic.[↔]-to-[←] IsTrue.preserves-[||][∨] (Either.map2 (Logic.[↔]-to-[←] IsTrue.preserves-[!][¬] ∘ Logic.contrapositiveᵣ (eval-to-models {φ = φ})) (models-to-eval {φ = ψ}) p))
  models-to-eval {φ = φ ⟷ ψ} p = [≡]-substitutionₗ Bool.[==]-disjunctive-form {f = IsTrue} (Logic.[↔]-to-[←] IsTrue.preserves-[||][∨] (Either.map2 (Logic.[↔]-to-[←] IsTrue.preserves-[&&][∧] ∘ Tuple.map (models-to-eval {φ = φ}) (models-to-eval {φ = ψ})) (Logic.[↔]-to-[←] IsTrue.preserves-[&&][∧] ∘ Tuple.map (Logic.[↔]-to-[←] IsTrue.preserves-[!][¬] ∘ Logic.contrapositiveᵣ (eval-to-models {φ = φ})) (Logic.[↔]-to-[←] IsTrue.preserves-[!][¬] ∘ Logic.contrapositiveᵣ (eval-to-models {φ = ψ}))) p))

  completeness : (Γ ⊨ φ) → (Γ ⊢ φ)
  completeness {φ = φ} Γφ {𝔐} a = models-to-eval {φ = φ} (Γφ (\{γ} → eval-to-models {φ = γ} ∘ a))

  soundness : (Γ ⊢ φ) → (Γ ⊨ φ)
  soundness {φ = φ} Γφ {𝔐} a = eval-to-models {φ = φ} (Γφ (\{γ} → models-to-eval {φ = γ} ∘ a))

module NaturalDeduction where
  {-data Tree : Formula → Stmt{Lvl.𝐒(ℓ)} where
    [⊤]-intro : Tree(⊤)

    [⊥]-intro : ∀{φ} → Tree(φ) → Tree(¬ φ) → Tree(⊥)
    [⊥]-elim  : ∀{φ} → Tree(⊥) → Tree(φ)

    [¬]-intro : ∀{Γ : Formulas}{φ} → ((Γ ∪ singleton(φ)) ⊢ ⊥) → Tree(¬ φ)
    [¬]-elim  : ∀{Γ : Formulas}{φ} → ((Γ ∪ singleton(¬ φ)) ⊢ ⊥) → Tree(φ)

    [∧]-intro : ∀{φ ψ} → Tree(φ) → Tree(ψ) → Tree(φ ∧ ψ)
    [∧]-elimₗ : ∀{φ ψ} → Tree(φ ∧ ψ) → Tree(φ)
    [∧]-elimᵣ : ∀{φ ψ} → Tree(φ ∧ ψ) → Tree(ψ)

    [∨]-introₗ : ∀{φ ψ} → Tree(φ) → Tree(φ ∨ ψ)
    [∨]-introᵣ : ∀{φ ψ} → Tree(ψ) → Tree(φ ∨ ψ)
    [∨]-elim   : ∀{Γ : Formulas}{φ ψ χ} → ((Γ ∪ singleton(φ)) ⊢ χ) → ((Γ ∪ singleton(ψ)) ⊢ χ) → Tree(φ ∨ ψ) → Tree(χ)

    [⟶]-intro : ∀{Γ : Formulas}{φ ψ} → ((Γ ∪ singleton(φ)) ⊢ ψ) → Tree(φ ⟶ ψ)
    [⟶]-elim  : ∀{Γ : Formulas}{φ ψ} → Tree(φ) → Tree(φ ⟶ ψ) → Tree(ψ)

    [⟷]-intro : ∀{Γ : Formulas}{φ ψ} → ((Γ ∪ singleton(ψ)) ⊢ φ) → ((Γ ∪ singleton(φ)) ⊢ ψ) → Tree(ψ ⟷ φ)
    [⟷]-elimₗ : ∀{φ ψ} → Tree(φ) → Tree(ψ ⟷ φ) → Tree(ψ)
    [⟷]-elimᵣ : ∀{φ ψ} → Tree(ψ) → Tree(ψ ⟷ φ) → Tree(φ)
  Tree-to-[⊢]-tautologies : ∀{φ} → Tree(φ) → (∅ ⊢ φ)
  Tree-to-[⊢]-tautologies {.⊤} [⊤]-intro = [⊤]-intro
  Tree-to-[⊢]-tautologies {.⊥} ([⊥]-intro tφ tφ₁) =
    ([⊥]-intro
      (Tree-to-[⊢]-tautologies tφ)
      (Tree-to-[⊢]-tautologies tφ₁)
    )
  Tree-to-[⊢]-tautologies {φ} ([⊥]-elim tφ) =
    ([⊥]-elim
      (Tree-to-[⊢]-tautologies tφ)
    )
  Tree-to-[⊢]-tautologies {.(¬ _)} ([¬]-intro x) = {!!}
  Tree-to-[⊢]-tautologies {φ} ([¬]-elim x) = {!!}
  Tree-to-[⊢]-tautologies {.(_ ∧ _)} ([∧]-intro tφ tφ₁) =
    ([∧]-intro
      (Tree-to-[⊢]-tautologies tφ)
      (Tree-to-[⊢]-tautologies tφ₁)
    )
  Tree-to-[⊢]-tautologies {φ} ([∧]-elimₗ tφ) =
    ([∧]-elimₗ
      (Tree-to-[⊢]-tautologies tφ)
    )
  Tree-to-[⊢]-tautologies {φ} ([∧]-elimᵣ tφ) =
    ([∧]-elimᵣ
      (Tree-to-[⊢]-tautologies tφ)
    )
  Tree-to-[⊢]-tautologies {.(_ ∨ _)} ([∨]-introₗ tφ) =
    ([∨]-introₗ
      (Tree-to-[⊢]-tautologies tφ)
    )
  Tree-to-[⊢]-tautologies {.(_ ∨ _)} ([∨]-introᵣ tφ) =
    ([∨]-introᵣ
      (Tree-to-[⊢]-tautologies tφ)
    )
  Tree-to-[⊢]-tautologies {φ} ([∨]-elim x x₁ tφ) = {!!}
  Tree-to-[⊢]-tautologies {.(_ ⟶ _)} ([⟶]-intro x) = {!!}
  Tree-to-[⊢]-tautologies {φ} ([⟶]-elim tφ tφ₁) =
    ([⟶]-elim
      (Tree-to-[⊢]-tautologies tφ)
      (Tree-to-[⊢]-tautologies tφ₁)
    )
  Tree-to-[⊢]-tautologies {.(_ ⟷ _)} ([⟷]-intro x x₁) = {!!}
  Tree-to-[⊢]-tautologies {φ} ([⟷]-elimₗ tφ tφ₁) =
    ([⟷]-elimₗ
      (Tree-to-[⊢]-tautologies tφ)
      (Tree-to-[⊢]-tautologies tφ₁)
    )
  Tree-to-[⊢]-tautologies {φ} ([⟷]-elimᵣ tφ tφ₁) =
    ([⟷]-elimᵣ
      (Tree-to-[⊢]-tautologies tφ)
      (Tree-to-[⊢]-tautologies tφ₁)
    )

  Tree-to-[⊢] : ∀{Γ : Formulas}{φ} → ((Γ ⊆ Tree) → Tree(φ)) → (Γ ⊢ φ)
  Tree-to-[⊢] {Γ} {φ} t = {!!}-}

  private variable P : Type{ℓₚ}
  private variable Γ Γ₁ Γ₂ : Formulas(P){ℓ}
  private variable φ ψ : Formula(P)

  data _⊢_ {ℓ ℓₚ} {P : Type{ℓₚ}} : Formulas(P){ℓ} → Formula(P) → Stmt{Lvl.𝐒(ℓₚ Lvl.⊔ ℓ)} where
    direct : ∀{Γ} → (Γ ⊆ (Γ ⊢_))

    [⊤]-intro : ∀{Γ} → (Γ ⊢ ⊤)

    [⊥]-intro : ∀{Γ}{φ} → (Γ ⊢ φ) → (Γ ⊢ (¬ φ)) → (Γ ⊢ ⊥)
    [⊥]-elim  : ∀{Γ}{φ} → (Γ ⊢ ⊥) → (Γ ⊢ φ)

    [¬]-intro : ∀{Γ}{φ} → ((Γ ∪ singleton(φ)) ⊢ ⊥) → (Γ ⊢ (¬ φ))
    [¬]-elim  : ∀{Γ}{φ} → ((Γ ∪ singleton(¬ φ)) ⊢ ⊥) → (Γ ⊢ φ)

    [∧]-intro : ∀{Γ}{φ ψ} → (Γ ⊢ φ) → (Γ ⊢ ψ) → (Γ ⊢ (φ ∧ ψ))
    [∧]-elimₗ : ∀{Γ}{φ ψ} → (Γ ⊢ (φ ∧ ψ)) → (Γ ⊢ φ)
    [∧]-elimᵣ : ∀{Γ}{φ ψ} → (Γ ⊢ (φ ∧ ψ)) → (Γ ⊢ ψ)

    [∨]-introₗ : ∀{Γ}{φ ψ} → (Γ ⊢ φ) → (Γ ⊢ (φ ∨ ψ))
    [∨]-introᵣ : ∀{Γ}{φ ψ} → (Γ ⊢ ψ) → (Γ ⊢ (φ ∨ ψ))
    [∨]-elim   : ∀{Γ}{φ ψ χ} → ((Γ ∪ singleton(φ)) ⊢ χ) → ((Γ ∪ singleton(ψ)) ⊢ χ) → (Γ ⊢ (φ ∨ ψ)) → (Γ ⊢ χ)

    [⟶]-intro : ∀{Γ}{φ ψ} → ((Γ ∪ singleton(φ)) ⊢ ψ) → (Γ ⊢ (φ ⟶ ψ))
    [⟶]-elim  : ∀{Γ}{φ ψ} → (Γ ⊢ φ) → (Γ ⊢ (φ ⟶ ψ)) → (Γ ⊢ ψ)

    [⟷]-intro : ∀{Γ}{φ ψ} → ((Γ ∪ singleton(ψ)) ⊢ φ) → ((Γ ∪ singleton(φ)) ⊢ ψ) → (Γ ⊢ (φ ⟷ ψ))
    [⟷]-elimₗ : ∀{Γ}{φ ψ} → (Γ ⊢ ψ) → (Γ ⊢ (φ ⟷ ψ)) → (Γ ⊢ φ)
    [⟷]-elimᵣ : ∀{Γ}{φ ψ} → (Γ ⊢ φ) → (Γ ⊢ (φ ⟷ ψ)) → (Γ ⊢ ψ)

  weaken-union-singleton : (Γ₁ ⊆ Γ₂) → (((Γ₁ ∪ singleton(φ)) ⊢_) ⊆ ((Γ₂ ∪ singleton(φ)) ⊢_))

  weaken : (Γ₁ ⊆ Γ₂) → ((Γ₁ ⊢_) ⊆ (Γ₂ ⊢_))
  weaken Γ₁Γ₂ {φ}        (direct p)         = direct (Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {.⊤}       [⊤]-intro          = [⊤]-intro
  weaken Γ₁Γ₂ {.⊥}       ([⊥]-intro  p q)   = [⊥]-intro  (weaken Γ₁Γ₂ p) (weaken Γ₁Γ₂ q)
  weaken Γ₁Γ₂ {φ}        ([⊥]-elim   p)     = [⊥]-elim   (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {.(¬ _)}   ([¬]-intro  p)     = [¬]-intro  (weaken-union-singleton Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {φ}        ([¬]-elim   p)     = [¬]-elim   (weaken-union-singleton Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {.(_ ∧ _)} ([∧]-intro  p q)   = [∧]-intro  (weaken Γ₁Γ₂ p) (weaken Γ₁Γ₂ q)
  weaken Γ₁Γ₂ {φ}        ([∧]-elimₗ  p)     = [∧]-elimₗ  (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {φ}        ([∧]-elimᵣ  p)     = [∧]-elimᵣ  (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {.(_ ∨ _)} ([∨]-introₗ p)     = [∨]-introₗ (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {.(_ ∨ _)} ([∨]-introᵣ p)     = [∨]-introᵣ (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {φ}        ([∨]-elim   p q r) = [∨]-elim   (weaken-union-singleton Γ₁Γ₂ p) (weaken-union-singleton Γ₁Γ₂ q) (weaken Γ₁Γ₂ r)
  weaken Γ₁Γ₂ {.(_ ⟶ _)} ([⟶]-intro  p)     = [⟶]-intro  (weaken-union-singleton Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {φ}        ([⟶]-elim   p q)   = [⟶]-elim   (weaken Γ₁Γ₂ p) (weaken Γ₁Γ₂ q)
  weaken Γ₁Γ₂ {.(_ ⟷ _)} ([⟷]-intro  p q)   = [⟷]-intro  (weaken-union-singleton Γ₁Γ₂ p) (weaken-union-singleton Γ₁Γ₂ q)
  weaken Γ₁Γ₂ {φ}        ([⟷]-elimₗ  p q)   = [⟷]-elimₗ  (weaken Γ₁Γ₂ p) (weaken Γ₁Γ₂ q)
  weaken Γ₁Γ₂ {φ}        ([⟷]-elimᵣ  p q)   = [⟷]-elimᵣ  (weaken Γ₁Γ₂ p) (weaken Γ₁Γ₂ q)

  weaken-union-singleton Γ₁Γ₂ p = weaken (Either.mapLeft Γ₁Γ₂) p

  weaken-union : (Γ₁ ⊢_) ⊆ ((Γ₁ ∪ Γ₂) ⊢_)
  weaken-union = weaken Either.Left

  [⟵]-intro : ((Γ ∪ singleton(φ)) ⊢ ψ) → (Γ ⊢ (ψ ⟵ φ))
  [⟵]-intro = [⟶]-intro

  [⟵]-elim : (Γ ⊢ φ) → (Γ ⊢ (ψ ⟵ φ)) → (Γ ⊢ ψ)
  [⟵]-elim = [⟶]-elim

  [¬¬]-elim : (Γ ⊢ ¬(¬ φ)) → (Γ ⊢ φ)
  [¬¬]-elim nnφ =
    ([¬]-elim
      ([⊥]-intro
        (direct(Right [≡]-intro))
        (weaken-union nnφ)
      )
    )

  [¬¬]-intro : (Γ ⊢ φ) → (Γ ⊢ ¬(¬ φ))
  [¬¬]-intro Γφ =
    ([¬]-intro
      ([⊥]-intro
        (weaken-union Γφ)
        (direct (Right [≡]-intro))
      )
    )

  _⊬_ : Formulas(P){ℓ} → Formula(P) → Stmt
  _⊬_ = Logic.¬_ ∘₂ _⊢_

  [¬]-intro-converse : ((Γ ∪ singleton(φ)) ⊢ ⊥) ← (Γ ⊢ (¬ φ))
  [¬]-intro-converse {Γ = Γ}{φ = φ} Γ¬φ = [⊥]-intro (direct (Right [≡]-intro)) (weaken-union Γ¬φ)

  excluded-middle : Γ ⊢ (φ ∨ (¬ φ))
  excluded-middle =
    ([¬¬]-elim
      ([¬]-intro
        ([⊥]-intro
          ([∨]-introᵣ
            ([¬]-intro
              ([⊥]-intro
                ([∨]-introₗ (direct (Right [≡]-intro)))
                (direct (Left (Right [≡]-intro)))
              )
            )
          )
          (direct (Right [≡]-intro))
        )
      )
    )

  [→]-disjunctive-form : (Γ ⊢ (φ ⟶ ψ)) Logic.↔ (Γ ⊢ ((¬ φ) ∨ ψ))
  [→]-disjunctive-form = Logic.[↔]-intro l r where
    l = [∨]-elim
      ([⟶]-intro ([⊥]-elim ([⊥]-intro
        (direct (Right [≡]-intro))
        (direct (Left (Right [≡]-intro)))
      )))
      ([⟶]-intro (direct (Left (Right [≡]-intro))))
    r = pq ↦
      ([∨]-elim
        ([∨]-introᵣ ([⟶]-elim (direct (Right [≡]-intro)) (weaken Left pq)))
        ([∨]-introₗ (direct (Right [≡]-intro)))
        excluded-middle
      )

  [⟷]-negated : (Γ ⊢ (φ ⟷ ψ)) → (Γ ⊢ ((¬ φ) ⟷ (¬ ψ)))
  [⟷]-negated p = [⟷]-intro
    ([¬]-intro ([⊥]-intro ([⟷]-elimᵣ (direct (Right [≡]-intro)) (weaken (Left ∘ Left) p)) (direct (Left (Right [≡]-intro)))))
    (([¬]-intro ([⊥]-intro ([⟷]-elimₗ (direct (Right [≡]-intro)) (weaken (Left ∘ Left) p)) (direct (Left (Right [≡]-intro))))))

  [⟷]-conjunction-disjunction-negation : (Γ ⊢ (φ ⟷ ψ)) Logic.↔ (Γ ⊢ ((φ ∧ ψ) ∨ ((¬ φ) ∧ (¬ ψ))))
  [⟷]-conjunction-disjunction-negation = Logic.[↔]-intro l r where
    l = [∨]-elim
      ([⟷]-intro
        ([∧]-elimₗ (direct (Left (Right [≡]-intro))))
        ([∧]-elimᵣ (direct (Left (Right [≡]-intro))))
      )
      ([⟷]-intro
        ([⊥]-elim ([⊥]-intro (direct (Right [≡]-intro)) ([∧]-elimᵣ (direct (Left (Right [≡]-intro))))))
        ([⊥]-elim ([⊥]-intro (direct (Right [≡]-intro)) ([∧]-elimₗ (direct (Left (Right [≡]-intro))))))
      )
    r = p ↦ [∨]-elim
      ([∨]-introₗ ([∧]-intro
        (direct (Right [≡]-intro))
        ([⟷]-elimᵣ (direct (Right [≡]-intro)) (weaken Left p))
      ))
      ([∨]-introᵣ ([∧]-intro
        (direct (Right [≡]-intro))
        ([⟷]-elimᵣ (direct (Right [≡]-intro)) (weaken Left ([⟷]-negated p)))
      ))
      excluded-middle

  Inconsistent : Formulas(P){ℓ} → Stmt
  Inconsistent(Γ) = Γ ⊢ ⊥

  Consistent : Formulas(P){ℓ} → Stmt
  Consistent(Γ) = Γ ⊬ ⊥ 

  consistency-of-[∪]ₗ : Consistent(Γ₁ ∪ Γ₂) → Consistent(Γ₁)
  consistency-of-[∪]ₗ con z = con (weaken-union z)

  -- TODO: Replace all occurrences of "consistence" with "consistency", and "deriviability" with "derivability"
  [⊢]-deriviability-inconsistence : (Γ ⊢ φ) Logic.↔ Inconsistent(Γ ∪ singleton(¬ φ))
  [⊢]-deriviability-inconsistence = Logic.[↔]-intro [¬]-elim ([¬]-intro-converse ∘ [¬¬]-intro)

  [⊢]-deriviability-consistenceᵣ : Consistent(Γ) → ((Γ ⊢ φ) → Consistent(Γ ∪ singleton(φ)))
  [⊢]-deriviability-consistenceᵣ con Γφ Γφ⊥ = con([⊥]-intro Γφ ([¬]-intro Γφ⊥))

  [⊢]-explosion-inconsistence : (∀{φ} → (Γ ⊢ φ)) Logic.↔ Inconsistent(Γ)
  [⊢]-explosion-inconsistence {Γ} = Logic.[↔]-intro (λ z → [⊥]-elim z) (λ z → z)

  [⊢]-functionₗ : (Γ₁ ≡ₛ Γ₂) → ((Γ₁ ⊢_) ≡ₛ (Γ₂ ⊢_))
  [⊢]-functionₗ Γ₁Γ₂ = Logic.[↔]-intro (weaken (Logic.[↔]-to-[←] Γ₁Γ₂)) (weaken (Logic.[↔]-to-[→] Γ₁Γ₂))

  [⊢]-compose : (Γ ⊢ φ) → ((Γ ∪ singleton(φ)) ⊢ ψ) → (Γ ⊢ ψ)
  [⊢]-compose Γφ Γφψ = [∨]-elim Γφψ Γφψ ([∨]-introₗ Γφ)

  [⊢]-compose-inconsistence : (Γ ⊢ φ) → Inconsistent(Γ ∪ singleton(φ)) → Inconsistent(Γ)
  [⊢]-compose-inconsistence Γφ Γφ⊥ = [⊥]-intro Γφ ([¬]-intro Γφ⊥)

  [⊢]-compose-consistence : (Γ ⊢ φ) → Consistent(Γ) → Consistent(Γ ∪ singleton(φ))
  [⊢]-compose-consistence Γφ = Logic.contrapositiveᵣ ([⊢]-compose-inconsistence Γφ)

  [⊢]-subset-consistency : (Γ₁ ⊆ Γ₂) → (Consistent(Γ₂) → Consistent(Γ₁))
  [⊢]-subset-consistency sub con = con ∘ weaken sub

  [⊢]-subset-inconsistency : (Γ₁ ⊆ Γ₂) → (Inconsistent(Γ₁) → Inconsistent(Γ₂))
  [⊢]-subset-inconsistency sub = weaken sub

  [⊬]-derives-negation-consistency : (Γ ⊬ (¬ φ)) → Consistent(Γ ∪ singleton(φ))
  [⊬]-derives-negation-consistency = _∘ [¬]-intro

  {- TODO: Maybe by soundness?
  consistency-of-∅ : Consistent{P = P}{ℓ = ℓ}(∅)
  consistency-of-∅ ([⊥]-intro {φ = • x} p q) = {!!}
  consistency-of-∅ ([⊥]-intro {φ = ⊤} p q) = {![¬]-elim!}
  consistency-of-∅ ([⊥]-intro {φ = ⊥} p q) = {!!}
  consistency-of-∅ ([⊥]-intro {φ = ¬ φ} p q) = {!!}
  consistency-of-∅ ([⊥]-intro {φ = φ ∧ φ₁} p q) = {!!}
  consistency-of-∅ ([⊥]-intro {φ = φ ∨ φ₁} p q) = {!!}
  consistency-of-∅ ([⊥]-intro {φ = φ ⟶ φ₁} p q) = {!!}
  consistency-of-∅ ([⊥]-intro {φ = φ ⟷ φ₁} p q) = {!!}
  consistency-of-∅ ([⊥]-elim  p)     = consistency-of-∅ p
  consistency-of-∅ ([¬]-elim  p)     = consistency-of-∅ ([⊢]-compose-inconsistence ([¬]-intro (direct (Right [≡]-intro))) p)
  consistency-of-∅ ([∧]-elimₗ p)     = consistency-of-∅ {!!}
  consistency-of-∅ ([∧]-elimᵣ p)     = {!!}
  consistency-of-∅ ([∨]-elim  p q r) = {!!}
  consistency-of-∅ ([⟶]-elim  p q)   = {!!}
  consistency-of-∅ ([⟷]-elimₗ p q)   = {!!}
  consistency-of-∅ ([⟷]-elimᵣ p q)   = {!!}
  -}

  -- TODO: Is this provable? Does one need to include it in the definition of (_⊢_)? Is it even possible to include it?
  -- [⊢]-hypothesis : ((Γ ⊢ φ) → (Γ ⊢ ψ)) → ((Γ ∪ singleton(φ)) ⊢ ψ)
  -- [⊢]-hypothesis hyp = {!!}

  [⊢][→]-intro-from-[∨] : (Γ ⊢ ¬ φ) Logic.∨ (Γ ⊢ ψ) → (Γ ⊢ (φ ⟶ ψ))
  [⊢][→]-intro-from-[∨] {Γ = Γ}{φ}{ψ} (Left x) = [⟶]-intro ([⊥]-elim ([⊥]-intro (direct (Right [≡]-intro)) (weaken-union {Γ₂ = singleton φ} x)))
  [⊢][→]-intro-from-[∨] (Right x) = [⟶]-intro (weaken-union x)

  -- A smallest finite set of assumptions that is able to derive a formula.
  finiteAssumptions : ∀{φ : Formula(P)} → (Γ ⊢ φ) → Formulas(P){Lvl.of(P)}
  finiteAssumptions {φ = φ}        (direct _)                  = singleton(φ)
  finiteAssumptions {φ = .⊤}       [⊤]-intro                   = ∅
  finiteAssumptions {φ = .⊥}       ([⊥]-intro           p q)   = finiteAssumptions p ∪ finiteAssumptions q
  finiteAssumptions {φ = φ}        ([⊥]-elim            p)     = finiteAssumptions p
  finiteAssumptions {φ = ¬ φ}      ([¬]-intro{φ = φ}    p)     = finiteAssumptions p ∖ singleton(φ)
  finiteAssumptions {φ = φ}        ([¬]-elim {φ = φ}    p)     = finiteAssumptions p ∖ singleton(¬ φ)
  finiteAssumptions {φ = .(_ ∧ _)} ([∧]-intro           p q)   = finiteAssumptions p ∪ finiteAssumptions q
  finiteAssumptions {φ = φ}        ([∧]-elimₗ           p)     = finiteAssumptions p
  finiteAssumptions {φ = φ}        ([∧]-elimᵣ           p)     = finiteAssumptions p
  finiteAssumptions {φ = .(_ ∨ _)} ([∨]-introₗ          p)     = finiteAssumptions p
  finiteAssumptions {φ = .(_ ∨ _)} ([∨]-introᵣ          p)     = finiteAssumptions p
  finiteAssumptions {φ = _}        ([∨]-elim {φ = φ}{ψ} p q r) = ((finiteAssumptions p ∖ singleton(φ)) ∪ (finiteAssumptions q ∖ singleton(ψ))) ∪ finiteAssumptions r
  finiteAssumptions {φ = .(_ ⟶ _)} ([⟶]-intro{φ = φ}    p)     = finiteAssumptions p ∖ singleton(φ)
  finiteAssumptions {φ = φ}        ([⟶]-elim            p q)   = finiteAssumptions p ∪ finiteAssumptions q
  finiteAssumptions {φ = .(_ ⟷ _)} ([⟷]-intro{φ = φ}{ψ} p q)   = (finiteAssumptions p ∖ singleton(ψ)) ∪ (finiteAssumptions q ∖ singleton(φ))
  finiteAssumptions {φ = φ}        ([⟷]-elimₗ           p q)   = finiteAssumptions p ∪ finiteAssumptions q
  finiteAssumptions {φ = φ}        ([⟷]-elimᵣ           p q)   = finiteAssumptions p ∪ finiteAssumptions q

  -- TODO: These should be in SetLike
  module _ where
    private variable X : Type{ℓ}
    private variable A A₁ A₂ B B₁ B₂ C : X → Type{ℓ}

    [∪]-subset : (A ⊆ C) → (B ⊆ C) → ((A ∪ B) ⊆ C)
    [∪]-subset ac bc = Logic.[∨]-elim ac bc

    [∪]-subset2 : (A₁ ⊆ A₂) → (B₁ ⊆ B₂) → ((A₁ ∪ B₁) ⊆ (A₂ ∪ B₂))
    [∪]-subset2 aa bb = Logic.[∨]-elim2 aa bb

    [∖][∪]-is-[∪] : (((A ∖ B) ∪ B) ≡ₛ (A ∪ B))
    [∖][∪]-is-[∪] {A = A}{B = B}{x = x} =
      Logic.[↔]-intro
        (Logic.[∨]-elim (Ax ↦ Logic.[∨]-elim2 (Logic.[∧]-intro Ax) id (Logic.[∨]-symmetry(Logic.excluded-middle(B(x))))) Logic.[∨]-introᵣ)
        (Logic.[∨]-elim (Logic.[∨]-introₗ ∘ Logic.[∧]-elimₗ) Logic.[∨]-introᵣ) -- TODO: This direction does not require a classical setting

    [∪][∖]-invertᵣ-[⊆] : (A ⊆ (B ∪ C)) → ((A ∖ C) ⊆ B)
    [∪][∖]-invertᵣ-[⊆] abc (Logic.[∧]-intro a nc) = Logic.[∨]-elim id (Logic.[⊥]-elim ∘ nc) (abc a)

  finiteAssumptions-correctness : (p : (Γ ⊢ φ)) → (finiteAssumptions p ⊢ φ)
  finiteAssumptions-correctness (direct x)         = direct [≡]-intro
  finiteAssumptions-correctness [⊤]-intro          = [⊤]-intro
  finiteAssumptions-correctness ([⊥]-intro  p q)   = [⊥]-intro (weaken Left (finiteAssumptions-correctness p)) (weaken Right (finiteAssumptions-correctness q))
  finiteAssumptions-correctness ([⊥]-elim   p)     = [⊥]-elim (finiteAssumptions-correctness p)
  finiteAssumptions-correctness ([¬]-intro  p)     = [¬]-intro (weaken (Logic.[↔]-to-[←] ([∖][∪]-is-[∪] {A = finiteAssumptions p}{B = singleton _}) ∘ Logic.[∨]-introₗ) (finiteAssumptions-correctness p))
  finiteAssumptions-correctness ([¬]-elim   p)     = [¬]-elim (weaken (Logic.[↔]-to-[←] ([∖][∪]-is-[∪] {A = finiteAssumptions p}{B = singleton _}) ∘ Logic.[∨]-introₗ) (finiteAssumptions-correctness p))
  finiteAssumptions-correctness ([∧]-intro  p q)   = [∧]-intro (weaken Left (finiteAssumptions-correctness p)) (weaken Right (finiteAssumptions-correctness q))
  finiteAssumptions-correctness ([∧]-elimₗ  p)     = [∧]-elimₗ (finiteAssumptions-correctness p)
  finiteAssumptions-correctness ([∧]-elimᵣ  p)     = [∧]-elimᵣ (finiteAssumptions-correctness p)
  finiteAssumptions-correctness ([∨]-introₗ p)     = [∨]-introₗ (finiteAssumptions-correctness p)
  finiteAssumptions-correctness ([∨]-introᵣ p)     = [∨]-introᵣ (finiteAssumptions-correctness p)
  finiteAssumptions-correctness ([∨]-elim{φ = φ}{ψ} p q r) = [∨]-elim (weaken (sl ∘ Left) (finiteAssumptions-correctness p)) (weaken (sr ∘ Left) (finiteAssumptions-correctness q)) (weaken Right (finiteAssumptions-correctness r)) where
    sl : (finiteAssumptions p ∪ singleton(φ)) ⊆ ((((finiteAssumptions p ∖ singleton(φ)) ∪ (finiteAssumptions q ∖ singleton(ψ))) ∪ finiteAssumptions r) ∪ singleton(φ))
    sr : (finiteAssumptions q ∪ singleton(ψ)) ⊆ ((((finiteAssumptions p ∖ singleton(φ)) ∪ (finiteAssumptions q ∖ singleton(ψ))) ∪ finiteAssumptions r) ∪ singleton(ψ))
  finiteAssumptions-correctness ([⟶]-intro  p)     = [⟶]-intro (weaken (Logic.[↔]-to-[←] ([∖][∪]-is-[∪] {A = finiteAssumptions p}{B = singleton _}) ∘ Logic.[∨]-introₗ) (finiteAssumptions-correctness p))
  finiteAssumptions-correctness ([⟶]-elim   p q)   = [⟶]-elim (weaken Left (finiteAssumptions-correctness p)) (weaken Right (finiteAssumptions-correctness q))
  finiteAssumptions-correctness ([⟷]-intro  p q)   = [⟷]-intro (weaken (sl ∘ Left) (finiteAssumptions-correctness p)) (weaken (sr ∘ Left) (finiteAssumptions-correctness q)) where
    sl : (finiteAssumptions p ∪ singleton(φ)) ⊆ (((finiteAssumptions p ∖ singleton(φ)) ∪ (finiteAssumptions q ∖ singleton(ψ))) ∪ singleton(φ))
    sr : (finiteAssumptions q ∪ singleton(ψ)) ⊆ (((finiteAssumptions p ∖ singleton(φ)) ∪ (finiteAssumptions q ∖ singleton(ψ))) ∪ singleton(ψ))
  finiteAssumptions-correctness ([⟷]-elimₗ  p q)   = [⟷]-elimₗ (weaken Left (finiteAssumptions-correctness p)) (weaken Right (finiteAssumptions-correctness q))
  finiteAssumptions-correctness ([⟷]-elimᵣ  p q)   = [⟷]-elimᵣ (weaken Left (finiteAssumptions-correctness p)) (weaken Right (finiteAssumptions-correctness q))

  finiteAssumptions-subset : (p : (Γ ⊢ φ)) → (finiteAssumptions p ⊆ Γ)
  finiteAssumptions-subset        (direct x)         = \{[≡]-intro → x}
  finiteAssumptions-subset        [⊤]-intro          = empty
  finiteAssumptions-subset        ([⊥]-intro  p q)   = [∪]-subset (\{x} → finiteAssumptions-subset p {x}) (\{x} → finiteAssumptions-subset q {x})
  finiteAssumptions-subset        ([⊥]-elim   p)     = finiteAssumptions-subset p
  finiteAssumptions-subset        ([¬]-intro  p)     = [∪][∖]-invertᵣ-[⊆] {A = finiteAssumptions p} (finiteAssumptions-subset p)
  finiteAssumptions-subset        ([¬]-elim   p)     = [∪][∖]-invertᵣ-[⊆] {A = finiteAssumptions p} (finiteAssumptions-subset p)
  finiteAssumptions-subset        ([∧]-intro  p q)   = [∪]-subset (\{x} → finiteAssumptions-subset p {x}) (\{x} → finiteAssumptions-subset q {x})
  finiteAssumptions-subset        ([∧]-elimₗ  p)     = finiteAssumptions-subset p
  finiteAssumptions-subset        ([∧]-elimᵣ  p)     = finiteAssumptions-subset p
  finiteAssumptions-subset        ([∨]-introₗ p)     = finiteAssumptions-subset p
  finiteAssumptions-subset        ([∨]-introᵣ p)     = finiteAssumptions-subset p
  finiteAssumptions-subset{Γ = Γ} ([∨]-elim   p q r) = [∪]-subset (\{x} → [∪]-subset{C = Γ} ([∪][∖]-invertᵣ-[⊆] {B = Γ} (finiteAssumptions-subset p)) ([∪][∖]-invertᵣ-[⊆] {B = Γ} (finiteAssumptions-subset q)) {x}) (finiteAssumptions-subset r)
  finiteAssumptions-subset        ([⟶]-intro  p)     = \{(Logic.[∧]-intro fpx φx) → Logic.[∨]-elim id (Logic.[⊥]-elim ∘ φx) (finiteAssumptions-subset p fpx)}
  finiteAssumptions-subset        ([⟶]-elim   p q)   = [∪]-subset (\{x} → finiteAssumptions-subset p {x}) (\{x} → finiteAssumptions-subset q {x})
  finiteAssumptions-subset        ([⟷]-intro  p q)   = Logic.[∨]-elim ([∪][∖]-invertᵣ-[⊆] {A = finiteAssumptions p} (finiteAssumptions-subset p)) ([∪][∖]-invertᵣ-[⊆] {A = finiteAssumptions q} (finiteAssumptions-subset q))
  finiteAssumptions-subset        ([⟷]-elimₗ  p q)   = [∪]-subset (\{x} → finiteAssumptions-subset p {x}) (\{x} → finiteAssumptions-subset q {x})
  finiteAssumptions-subset        ([⟷]-elimᵣ  p q)   = [∪]-subset (\{x} → finiteAssumptions-subset p {x}) (\{x} → finiteAssumptions-subset q {x})

  {-
  module _ where
    open import Numeral.Natural

    finiteAssumptions-index : (p : (Γ ⊢ φ)) → ∀{x} → (x ∈ finiteAssumptions p) → ℕ
    finiteAssumptions-index (direct x) [≡]-intro = {!!}
    finiteAssumptions-index [⊤]-intro ()
    finiteAssumptions-index ([⊥]-intro p q) (Left x) = {!!}
    finiteAssumptions-index ([⊥]-intro p q) (Right x) = {!!}
    finiteAssumptions-index ([⊥]-elim p) = {!!}
    finiteAssumptions-index ([¬]-intro p) = {!!}
    finiteAssumptions-index ([¬]-elim p) = {!!}
    finiteAssumptions-index ([∧]-intro p p₁) = {!!}
    finiteAssumptions-index ([∧]-elimₗ p) = {!!}
    finiteAssumptions-index ([∧]-elimᵣ p) = {!!}
    finiteAssumptions-index ([∨]-introₗ p) = {!!}
    finiteAssumptions-index ([∨]-introᵣ p) = {!!}
    finiteAssumptions-index ([∨]-elim p p₁ p₂) = {!!}
    finiteAssumptions-index ([⟶]-intro p) = {!!}
    finiteAssumptions-index ([⟶]-elim p p₁) = {!!}
    finiteAssumptions-index ([⟷]-intro p p₁) = {!!}
    finiteAssumptions-index ([⟷]-elimₗ p p₁) = {!!}
    finiteAssumptions-index ([⟷]-elimᵣ p p₁) = {!!}
  -}

  record MaximallyConsistent (Γ : Formulas(P){ℓ}) : Stmt{Lvl.𝐒(Lvl.of(P) Lvl.⊔ ℓ)} where
    field
      consistent : Consistent(Γ)
      --maximal    : ∀{Δ : Formulas(P)} → Consistent(Γ ∪ Δ) → (Δ ⊆ Γ)

      element-maximal : Consistent(Γ ∪ singleton(φ)) → (φ ∈ Γ)
      -- element-maximal con = maximal con [≡]-intro

    element-maximal-contra : (φ ∉ Γ) → Inconsistent(Γ ∪ singleton(φ))
    element-maximal-contra = Logic.[↔]-to-[←] Logic.contrapositive-variant2 element-maximal

    [⊢]-deriviability-consistenceₗ : ((Γ ⊢ φ) ← Consistent(Γ ∪ singleton(φ)))
    [⊢]-deriviability-consistenceₗ = direct ∘ element-maximal

    [⊢]-to-[∈] : (Γ ⊢ φ) → (φ ∈ Γ)
    [⊢]-to-[∈] = Logic.[→]-from-contrary (λ Γφ φ∉Γ → consistent ([⊢]-compose-inconsistence Γφ (element-maximal-contra φ∉Γ)))

    [⊢][∈]-equivalence : (Γ ⊢ φ) Logic.↔ (φ ∈ Γ)
    [⊢][∈]-equivalence = Logic.[↔]-intro direct [⊢]-to-[∈]

    -- excluded-middle-maximal-membership : ∀{φ} → (φ ∈ Γ) Logic.∨ ((¬ φ) ∈ Γ)

    {-r : (term-model(max Γ con) ⊧ φ) → (φ ∈ max Γ con)
    r {• x}   modelsφ Γφ-incons = Logic.[↔]-to-[←] Logic.decide-is-true modelsφ Γφ-incons
    r {⊤}     modelsφ Γφ-incons = con([⊢]-compose-inconsistence [⊤]-intro Γφ-incons)-}

    -- [•]-maximal-membership : ((• p) ∈ Γ) Logic.↔ ?
    -- [•]-maximal-membership = 

    [⊤]-maximal-membership : (⊤ ∈ Γ) Logic.↔ Logic.⊤
    [⊤]-maximal-membership = Logic.[↔]-intro l r where
      l = const (element-maximal (Γ⊤-incons ↦ consistent([⊢]-compose-inconsistence [⊤]-intro Γ⊤-incons)))
      r = const Logic.[⊤]-intro

    [⊥]-maximal-membership : (⊥ ∈ Γ) Logic.↔ Logic.⊥
    [⊥]-maximal-membership = Logic.[↔]-intro l r where
      l = Logic.[⊥]-elim
      r = consistent ∘ direct

    [¬]-maximal-membership : ((¬ φ) ∈ Γ) Logic.↔ (φ ∉ Γ)
    [¬]-maximal-membership = Logic.[↔]-intro l r where
      l = [⊢]-to-[∈] ∘ [¬]-intro ∘ element-maximal-contra
      r = Γ¬φ ↦ Γφ ↦ consistent([⊥]-intro (direct Γφ) (direct Γ¬φ))

    [∧]-maximal-membership : ((φ ∧ ψ) ∈ Γ) Logic.↔ ((φ ∈ Γ) Logic.∧ (ψ ∈ Γ))
    [∧]-maximal-membership = Logic.[↔]-intro l r where
      l = \{(Logic.[∧]-intro φΓ ψΓ) → [⊢]-to-[∈] ([∧]-intro (direct φΓ) (direct ψΓ))}
      r = φψΓ ↦ Logic.[∧]-intro ([⊢]-to-[∈] ([∧]-elimₗ(direct φψΓ))) ([⊢]-to-[∈] ([∧]-elimᵣ(direct φψΓ)))

    [∨]-maximal-membership : ((φ ∨ ψ) ∈ Γ) Logic.↔ ((φ ∈ Γ) Logic.∨ (ψ ∈ Γ))
    [∨]-maximal-membership = Logic.[↔]-intro l r where
      l = Logic.[∨]-elim ([⊢]-to-[∈] ∘ [∨]-introₗ ∘ direct) ([⊢]-to-[∈] ∘ [∨]-introᵣ ∘ direct)
      r = Logic.contrapositiveₗ ⦃ classical ⦄ ((\{(Logic.[∧]-intro ¬φΓ ¬ψΓ) → φψΓ ↦ consistent([∨]-elim (element-maximal-contra ¬φΓ) (element-maximal-contra ¬ψΓ) (direct φψΓ))}) ∘ Logic.[↔]-to-[→] Logic.[¬]-preserves-[∨][∧])

    [⟶]-maximal-membership : ((φ ⟶ ψ) ∈ Γ) Logic.↔ ((φ ∉ Γ) Logic.∨ (ψ ∈ Γ))
    [⟶]-maximal-membership =
      Logic.[↔]-symmetry [⊢][∈]-equivalence ⦗ Logic.[↔]-transitivity ⦘ₗ
      [→]-disjunctive-form                  ⦗ Logic.[↔]-transitivity ⦘ₗ
      [⊢][∈]-equivalence                    ⦗ Logic.[↔]-transitivity ⦘ₗ
      [∨]-maximal-membership                ⦗ Logic.[↔]-transitivity ⦘ₗ
      Logic.[↔]-intro
        (Either.mapLeft (Logic.[↔]-to-[←] [¬]-maximal-membership))
        (Either.mapLeft ((Logic.[↔]-to-[→] [¬]-maximal-membership)))

    [⟷]-maximal-membership : ((φ ⟷ ψ) ∈ Γ) Logic.↔ (((φ ∈ Γ) Logic.∧ (ψ ∈ Γ)) Logic.∨ ((φ ∉ Γ) Logic.∧ (ψ ∉ Γ)))
    [⟷]-maximal-membership =
      Logic.[↔]-symmetry [⊢][∈]-equivalence ⦗ Logic.[↔]-transitivity ⦘ₗ
      [⟷]-conjunction-disjunction-negation  ⦗ Logic.[↔]-transitivity ⦘ₗ
      [⊢][∈]-equivalence                    ⦗ Logic.[↔]-transitivity ⦘ₗ
      [∨]-maximal-membership                ⦗ Logic.[↔]-transitivity ⦘ₗ
      Logic.[↔]-intro
        (Either.map2 (Logic.[↔]-to-[←] [∧]-maximal-membership) (Logic.[↔]-to-[←] [∧]-maximal-membership))
        (Either.map2 (Logic.[↔]-to-[→] [∧]-maximal-membership) (Logic.[↔]-to-[→] [∧]-maximal-membership))
                                            ⦗ Logic.[↔]-transitivity ⦘ₗ
      Logic.[↔]-intro
        (Either.mapRight (Tuple.map (Logic.[↔]-to-[←] [¬]-maximal-membership) (Logic.[↔]-to-[←] [¬]-maximal-membership)))
        (Either.mapRight (Tuple.map (Logic.[↔]-to-[→] [¬]-maximal-membership) (Logic.[↔]-to-[→] [¬]-maximal-membership)))

    equal-model-existence : Logic.∃(𝔐 ↦ (Γ ≡ₛ (𝔐 Semantics.⊧_)))
    equal-model-existence = Logic.[∃]-intro witness ⦃ Logic.[↔]-intro l r ⦄ where
      witness = (p ↦ Classical.decide{P = (• p) ∈ Γ} classical)

      l : (witness Semantics.⊧ φ) → (φ ∈ Γ)
      r : witness Semantics.⊧₊ Γ

      r {• x}   = Logic.[↔]-to-[→] Logic.decide-is-true
      r {⊤}     = Logic.[↔]-to-[→] [⊤]-maximal-membership
      r {⊥}     = Logic.[↔]-to-[→] [⊥]-maximal-membership
      r {¬ φ}   = Logic.contrapositiveᵣ l ∘ Logic.[↔]-to-[→] [¬]-maximal-membership
      r {φ ∧ ψ} = Tuple.map r r ∘ Logic.[↔]-to-[→] [∧]-maximal-membership
      r {φ ∨ ψ} = Either.map2 r r ∘ Logic.[↔]-to-[→] [∨]-maximal-membership
      r {φ ⟶ ψ} = Either.map2 (Logic.contrapositiveᵣ l) r ∘ Logic.[↔]-to-[→] [⟶]-maximal-membership
      r {φ ⟷ ψ} = Either.map2 (Tuple.map r r) (Tuple.map (Logic.contrapositiveᵣ l) (Logic.contrapositiveᵣ l)) ∘ Logic.[↔]-to-[→] [⟷]-maximal-membership
      
      l {• x}   = Logic.[↔]-to-[←] Logic.decide-is-true
      l {⊤}     = Logic.[↔]-to-[←] [⊤]-maximal-membership
      l {¬ φ}   = Logic.[↔]-to-[←] [¬]-maximal-membership ∘ Logic.contrapositiveᵣ r
      l {φ ∧ ψ} = Logic.[↔]-to-[←] [∧]-maximal-membership ∘ Tuple.map l l
      l {φ ∨ ψ} = Logic.[↔]-to-[←] [∨]-maximal-membership ∘ Either.map2 l l
      l {φ ⟶ ψ} = Logic.[↔]-to-[←] [⟶]-maximal-membership ∘ Either.map2 (Logic.contrapositiveᵣ r) l
      l {φ ⟷ ψ} = Logic.[↔]-to-[←] [⟷]-maximal-membership ∘ Either.map2 (Tuple.map l l) (Tuple.map (Logic.contrapositiveᵣ r) (Logic.contrapositiveᵣ r))

    satisfiable : Semantics.Satisfiable(Γ)
    satisfiable = Logic.[∃]-map-proof (\eq {φ} → Logic.[↔]-to-[→] (eq{φ})) equal-model-existence

  open MaximallyConsistent ⦃ … ⦄ using
    ( [⊢]-deriviability-consistenceₗ
    ; [⊤]-maximal-membership
    ; [⊥]-maximal-membership
    ; [¬]-maximal-membership
    ; [∧]-maximal-membership
    ; [∨]-maximal-membership
    ; [⟶]-maximal-membership
    ; [⟷]-maximal-membership
    ) public

  module _ ⦃ countable-P : CountablyInfinite P ⦄ where
    -- Also called: Lindenbaums' lemma
    open import Numeral.Natural
    private variable n : ℕ
    {-
    data maxi (Γ : Formulas(P){ℓ}) : ℕ → Formulas(P){Lvl.of(P) Lvl.⊔ ℓ} where
      base : Γ        ⊆ maxi Γ 𝟎
      step : maxi Γ n ⊆ maxi Γ (𝐒(n))
      form : let ψ = Logic.[∃]-witness (Formula-is-countably-infinite {P = P}) n
             in  maxi Γ (𝐒(n)) (if Logic.decide(maxi Γ n ⊢ ψ) then ψ else (¬ ψ))

    maxi-zero : (Γ ≡ₛ maxi Γ 𝟎)
    maxi-zero = Logic.[↔]-intro (\{(base p) → p}) base

    maxi-succ : let ψ = Logic.[∃]-witness (Formula-is-countably-infinite {P = P}) n in (((maxi Γ n) ∪ singleton(if Logic.decide(maxi Γ n ⊢ ψ) then ψ else (¬ ψ))) ≡ₛ maxi Γ (𝐒(n)))
    maxi-succ {n = n}{Γ = Γ} = Logic.[↔]-intro l r where
      p = Logic.[∃]-witness (Formula-is-countably-infinite {P = P}) n

      l : ((maxi Γ n) ∪ singleton(if Logic.decide(maxi Γ n ⊢ p) then p else (¬ p))) ⊇ maxi Γ (𝐒(n))
      l (step x) = Left x
      l form     = Right [≡]-intro

      r : ((maxi Γ n) ∪ singleton(if Logic.decide(maxi Γ n ⊢ p) then p else (¬ p))) ⊆ maxi Γ (𝐒(n))
      r (Left x)          = step x
      r (Right [≡]-intro) = form

    maxi-superset : Consistent(Γ) → (∀{n} → (Γ ⊆ maxi Γ n))
    maxi-superset {Γ = Γ} con {𝟎} = Logic.[↔]-to-[→] maxi-zero
    maxi-superset {Γ = Γ} con {𝐒 n} {φ} Γφ = {!!}

    instance
      maxi-consistent : Consistent(Γ) → (∀{n} → Consistent(maxi Γ n))
      maxi-consistent         con {n = 𝟎}   = [⊢]-subset-consistency (Logic.[↔]-to-[←] maxi-zero) con
      maxi-consistent {Γ = Γ} con {n = 𝐒 n} = [⊢]-subset-consistency (Logic.[↔]-to-[←] maxi-succ) con-eq where
        p = Logic.[∃]-witness (Formula-is-countably-infinite {P = P}) n
        con-eq : Consistent((maxi Γ n) ∪ singleton(if Logic.decide(maxi Γ n ⊢ p) then p else (¬ p)))
        con-eq with Logic.excluded-middle(maxi Γ n ⊢ p) | Logic.decide(maxi Γ n ⊢ p)
        ... | Left  derp  | _ = [⊢]-compose-consistence derp (maxi-consistent con {n = n})
        ... | Right dernp | _ = [⊬]-derives-negation-consistency(dernp ∘ [¬¬]-elim)
    -}
    
    maxi2 : Formulas(P){ℓ} → ℕ → Formulas(P){Lvl.of(P) Lvl.⊔ ℓ}
    maxi2 Γ 𝟎      = Lvl.Up{Lvl.of(P)} ∘ Γ
    maxi2 Γ (𝐒(n)) = let ψ = Logic.[∃]-witness (Formula-is-countably-infinite {P = P}) n
                     in  (maxi2 Γ n) ∪ singleton(if Logic.decide(maxi2 Γ n ⊢ ψ) then ψ else (¬ ψ))

    maxi2-succ : let ψ = Logic.[∃]-witness (Formula-is-countably-infinite {P = P}) n in (((maxi2 Γ n) ∪ singleton(if Logic.decide(maxi2 Γ n ⊢ ψ) then ψ else (¬ ψ))) ≡ₛ maxi2 Γ (𝐒(n)))
    -- maxi2-succ {n = n}{Γ = Γ} = Logic.[↔]-intro {!!} {!!}

    maxi2-zero : (Γ ≡ₛ maxi2 Γ 𝟎)
    maxi2-zero {Γ = Γ} = Logic.[↔]-symmetry (Sets.PredicateSet.LvlUp-set-equality {S = Γ})

    maxi2-superset : Consistent(Γ) → (∀{n} → (Γ ⊆ maxi2 Γ n))
    maxi2-superset {Γ = Γ} con {𝟎}   = Logic.[↔]-to-[→] (maxi2-zero {Γ = Γ})
    maxi2-superset {Γ = Γ} con {𝐒 n} = Left ∘ maxi2-superset {Γ = Γ} con {n}

    instance
      maxi2-consistent : Consistent(Γ) → (∀{n} → Consistent(maxi2 Γ n))
      maxi2-consistent {Γ = Γ} con {n = 𝟎}   = [⊢]-subset-consistency (Logic.[↔]-to-[←] (maxi2-zero {Γ = Γ})) con
      maxi2-consistent {Γ = Γ} con {n = 𝐒 n} = [⊢]-subset-consistency (Logic.[↔]-to-[←] (maxi2-succ {Γ = Γ})) con-eq where
        p = Logic.[∃]-witness (Formula-is-countably-infinite {P = P}) n
        con-eq : Consistent((maxi2 Γ n) ∪ singleton(if Logic.decide(maxi2 Γ n ⊢ p) then p else (¬ p)))
        con-eq with Logic.excluded-middle(maxi2 Γ n ⊢ p) | Logic.decide(maxi2 Γ n ⊢ p)
        ... | Left  derp  | _ = [⊢]-compose-consistence derp (maxi2-consistent con {n = n})
        ... | Right dernp | _ = [⊬]-derives-negation-consistency(dernp ∘ [¬¬]-elim)

    max : (Γ : Formulas(P){ℓ}) → Formulas(P){Lvl.of(P) Lvl.⊔ ℓ}
    max(Γ) φ = Logic.∃(n ↦ φ ∈ maxi2 Γ n)

    instance
      max-consistent : Consistent(Γ) → Consistent(max Γ)
      max-consistent {Γ = Γ} con = [⊢]-subset-consistency (Logic.[∃]-proof test5) (maxi2-consistent con {Logic.[∃]-witness test5}) where
        open import Numeral.Natural.Relation.Order
        open import Type.Properties.Inhabited

        test2 : (φ ∈ max Γ) → Logic.∃(n ↦ (φ ∈ maxi2 Γ n))
        test2 p = p

        test3a : ∀{φ} → Logic.∃(n ↦ ((φ ∈ max Γ) → (φ ∈ maxi2 Γ n)))
        test3a = Logic.[∃]-unrelatedᵣ-[→]ₗ ⦃ pos = intro ⦃ 𝟎 ⦄ ⦄ test2

        test3b : Logic.∃{Obj = Formula(P) → ℕ}(n ↦ (max Γ) ⊆ (φ ↦ φ ∈ maxi2 Γ (n(φ))))
        test3b = Logic.[∀][∃]-to-function-existence test3a

        test4 : ∀{a b} → (a ≤ b) → ∀{Γ : Formulas(P){ℓ}} → ((maxi2 Γ a) ⊆ (maxi2 Γ b))
        test4 {a = 𝟎}   {𝟎}   [≤]-minimum                  p = p
        test4 {a = 𝟎}   {𝐒 b} [≤]-minimum           {Γ}    p = Left(test4 {a = 𝟎}{b} [≤]-minimum {Γ} p)
        test4 {a = 𝐒 a} {𝐒 b} ([≤]-with-[𝐒] ⦃ ab ⦄) {Γ}    (Left p)  = Left (test4 {a = a}{b} ab p)
        test4 {a = 𝐒 a} {𝐒 b} ([≤]-with-[𝐒] ⦃ ab ⦄) {Γ}{φ} (Right p) = {!test4 {a = a}{b = b} ab {Γ ∪ singleton(if Logic.decide(maxi2 Γ b ⊢ β) then β else (¬ β))}{φ} ? !} where
          β = Logic.[∃]-witness Formula-is-countably-infinite b
        {-with Logic.excluded-middle(maxi2 Γ a ⊢ Logic.[∃]-witness Formula-is-countably-infinite a) | p
        ... | Left x | [≡]-intro = {!!}
        ... | Right x | q = test4 {a} {𝐒 b} {!!} {!!}-}

        -- TODO: Because test3 and test4
        test5 : Logic.∃(n ↦ (max Γ) ⊆ (maxi2 Γ n))

      -- with [∃]-intro n ⦃ pn ⦄ ← max Γ = {!!}
      -- [⊢]-subset-consistency (\{φ} → {!maxi2-consistent con {n = 𝟎}!}) {!con!}

    instance
      max-maximally-consistent : Consistent(Γ) → MaximallyConsistent(max Γ)
      MaximallyConsistent.consistent      (max-maximally-consistent con) = max-consistent con
      MaximallyConsistent.element-maximal (max-maximally-consistent con) = {!!}

    max-superset : Consistent(Γ) → (Γ ⊆ max Γ)
    max-superset con Γφ = Logic.[∃]-intro 𝟎 ⦃ maxi2-superset con {𝟎} Γφ ⦄

{-

  {-
  max : (Γ : Formulas(P){ℓ}) → Consistent(Γ) → Formulas(P){Lvl.𝐒(Lvl.of(P) Lvl.⊔ ℓ)}
  max Γ con φ = Consistent(Γ ∪ singleton(φ)) -- TODO: Probably not like this. The problem with this definition is that (Consistent(Γ ∪ singleton(φ)) → (Γ ⊢ φ)) is impossible to prove, and it is neccessary for proving that (max Γ con) for any Γ is a consistent set of formulas. This is related to the issue that if both (Γ ∪ singleton(φ)) and (Γ ∪ singleton(¬ φ)) is consistent, then both of them will be included. But this would lead to (max Γ cons) not necccesarily consistent.
  -- if decide(Consistent(Γ ∪ singleton(φ))) then (Γ ∪ singleton(φ)) else (Γ ∪ singleton(¬ φ))
  {-data max2 (Γ : Formulas(P){ℓ}) (con : Consistent(Γ)) : Formulas(P){Lvl.𝐒(Lvl.of(P) Lvl.⊔ ℓ)} where
    Positive : Consistent  (Γ ∪ singleton(φ)) → Inconsistent(Γ ∪ singleton(¬ φ)) → max2 Γ con φ
    Negative : Inconsistent(Γ ∪ singleton(φ)) → Consistent  (Γ ∪ singleton(¬ φ)) → max2 Γ con φ
  -}
  max2 : (Γ : Formulas(P){ℓ}) → Consistent(Γ) → Formulas(P){Lvl.𝐒(Lvl.of(P) Lvl.⊔ ℓ)}
  max2 Γ con φ = Consistent(Γ ∪ singleton(φ)) Logic.∧ Inconsistent(Γ ∪ singleton(¬ φ))

  max-maximal : ∀{con : Consistent(Γ)} → (φ ∈ max Γ con) Logic.∨ ((¬ φ) ∈ max Γ con)
  max-maximal {Γ = Γ}{φ = φ}{con = con} with Logic.excluded-middle(Inconsistent(Γ ∪ singleton(φ))) ⦃ classical ⦄
  ... | Logic.[∨]-introₗ  Γφ⊥ = Logic.[∨]-introᵣ (Γ¬φ⊥ ↦ Logic.[⊥]-elim(con ([⊥]-intro ([¬]-elim Γ¬φ⊥) ([¬]-intro Γφ⊥))))
  ... | Logic.[∨]-introᵣ ¬Γφ⊥ = Logic.[∨]-introₗ ¬Γφ⊥

  max-no-bottom : ∀{con : Consistent(Γ)} → (⊥ ∉ max Γ con)
  max-no-bottom = apply(direct(Right [≡]-intro))

  max-consistent-containment : ∀{con : Consistent(Γ)} → (φ ∈ max Γ con) → ((¬ φ) ∈ max Γ con) → Logic.⊥
  max-consistent-containment {Γ = Γ}{φ = φ}{con = con} ¬Γφ⊥ ¬Γ¬φ⊥ = ¬Γφ⊥ ([⊥]-intro (direct (Right [≡]-intro)) {!!})

  max-consistency-membership : ∀{con} → Consistent(Γ ∪ singleton(φ)) Logic.↔ (φ ∈ max Γ con)
  max-consistency-membership = Logic.[↔]-intro id id

  max-inconsistency-membership2 : ∀{con} → Inconsistent(Γ ∪ singleton(φ)) Logic.↔ (φ ∉ max Γ con)
  max-inconsistency-membership2 = Logic.[↔]-intro Logic.[¬¬]-elim apply

  test : ∀{con} → (φ ∉ max Γ con) → ((¬ φ) ∈ max Γ con)
  test {con = con} p = [⊢]-compose-consistence ([¬]-intro(Logic.[¬¬]-elim p)) con

  max-consistent : ∀{con : Consistent(Γ)} → Consistent(max Γ con)
  max-consistent {Γ = Γ} {con = con} = Logic.contrapositiveᵣ {!!} con
  {-max-consistent {Γ = Γ} {con = con} (direct x)        = max-no-bottom{con = con} x
  max-consistent {Γ = Γ} {con = con} ([⊥]-intro p q)   = {!max-consistent q!}
  max-consistent {Γ = Γ} {con = con} ([⊥]-elim  p)     = max-consistent{con = con} p
  max-consistent {Γ = Γ} {con = con} ([¬]-elim  p)     = {!!}
  max-consistent {Γ = Γ} {con = con} ([∧]-elimₗ p)     = {!max-consistent !}
  max-consistent {Γ = Γ} {con = con} ([∧]-elimᵣ p)     = {!!}
  max-consistent {Γ = Γ} {con = con} ([∨]-elim  p q r) = {!!}
  max-consistent {Γ = Γ} {con = con} ([⟶]-elim  p q)   = {!!}
  max-consistent {Γ = Γ} {con = con} ([⟷]-elimₗ p q)   = {!!}
  max-consistent {Γ = Γ} {con = con} ([⟷]-elimᵣ p q)   = {!!}-}

  {-
  test2 : ∀{con} → ((¬ φ) ∈ max Γ con) → (φ ∉ max Γ con)
  test2 {con = con} p q = {!!}

  test3 : ∀{con} → (max Γ con ⊢ φ) → (Γ ⊢ φ)
  test3 {Γ = Γ} {φ} {con = con} (direct x) = {!!}
  test3 {Γ = Γ} {.⊤} {con = con} [⊤]-intro = {!!}
  test3 {Γ = Γ} {.⊥} {con = con} ([⊥]-intro p p₁) = {!!}
  test3 {Γ = Γ} {φ} {con = con} ([⊥]-elim p) = {!!}
  test3 {Γ = Γ} {.(¬ _)} {con = con} ([¬]-intro p) = {!!}
  test3 {Γ = Γ} {φ} {con = con} ([¬]-elim p) = {!!}
  test3 {Γ = Γ} {.(_ ∧ _)} {con = con} ([∧]-intro p p₁) = {!!}
  test3 {Γ = Γ} {φ} {con = con} ([∧]-elimₗ p) = {!!}
  test3 {Γ = Γ} {φ} {con = con} ([∧]-elimᵣ p) = {!!}
  test3 {Γ = Γ} {.(_ ∨ _)} {con = con} ([∨]-introₗ p) = {!!}
  test3 {Γ = Γ} {.(_ ∨ _)} {con = con} ([∨]-introᵣ p) = {!!}
  test3 {Γ = Γ} {φ} {con = con} ([∨]-elim p p₁ p₂) = {!!}
  test3 {Γ = Γ} {.(_ ⟶ _)} {con = con} ([⟶]-intro p) = {!!}
  test3 {Γ = Γ} {φ} {con = con} ([⟶]-elim p p₁) = {!!}
  test3 {Γ = Γ} {.(_ ⟷ _)} {con = con} ([⟷]-intro p p₁) = {!!}
  test3 {Γ = Γ} {φ} {con = con} ([⟷]-elimₗ p p₁) = {!!}
  test3 {Γ = Γ} {φ} {con = con} ([⟷]-elimᵣ p p₁) = {!!}
  -}

  max-inconsistency-membership : ∀{con} → Inconsistent(Γ ∪ singleton(φ)) Logic.↔ ((¬ φ) ∈ max Γ con)
  max-inconsistency-membership {Γ = Γ}{φ = φ}{con = con} =
    Logic.double-negation ⦗ Logic.[↔]-transitivity ⦘ₗ
    Logic.[¬]-unaryOperator max-consistency-membership ⦗ Logic.[↔]-transitivity ⦘ₗ
    Logic.[↔]-intro
      ll
      (Γ¬φ-incons ↦ Γφ-incons ↦ con([⊥]-intro ([¬]-elim Γφ-incons) ([¬]-intro (Logic.[¬¬]-elim Γ¬φ-incons))))
    where
      ll : Logic.¬((Γ ∪ singleton(¬ φ)) ⊢ ⊥) → Logic.¬((Γ ∪ singleton(φ)) ⊢ ⊥) → Empty
      ll ¬φin φin = {!!}
      -- () ← ¬φin([⊥]-intro {!!} (direct (Right [≡]-intro)))
      -- con([⊥]-intro {!!} {!!})
      -- 
      -- {![⊥]-intro (direct φin) (direct ¬φin)!})
  -- Logic.contrapositiveₗ ⦃ classical ⦄ (Γ¬φ-incons ↦ Γφ-incons ↦ con([⊥]-intro ([¬]-elim (Logic.[¬¬]-elim Γ¬φ-incons)) ([¬]-intro Γφ-incons)))

  max-superset : ∀{con : Consistent(Γ)} → (Γ ⊆ max Γ con)
  max-superset {con = con} {x = φ} φΓ Γφ⊥ = con ([⊥]-intro (direct φΓ) ([¬]-intro Γφ⊥))

  -- TODO: Are there any easy ways to prove this?
  instance
    max-maximally-consistent : ∀{con : Consistent(Γ)} → MaximallyConsistent(max Γ con)
    MaximallyConsistent.consistent (max-maximally-consistent {con = con}) = max-consistent{con = con}
    MaximallyConsistent.element-maximal max-maximally-consistent p = {!!} -- max-consistency-membership {!Logic.contrapositive-variant2ₗ weaken-union-singleton!} -- max-consistency-membership {!p!}

  -- max-[⊢]-subset : ∀{con : Consistent(Γ)} → ((max Γ con ⊢_) ⊆ (Γ ⊢_))
  -- max-[⊢]-subset {con = con} p = {!!}
-}


module _ where
  open Semantics
  open Semantics.Proofs
  open NaturalDeduction

  private variable P : Type{ℓₚ}
  private variable φ ψ : Formula(P)

  module _ where
    private variable Γ Γ₁ Γ₂ : Formulas(P){ℓₚ}

    soundness : (Γ ⊢ φ) → (Γ ⊨ φ)
    soundness (direct Γφ) 𝔐Γ            = 𝔐Γ(Γφ)
    soundness [⊤]-intro                 = const(Logic.[⊤]-intro)
    soundness ([⊥]-intro Γφ Γ¬φ) 𝔐Γ     = (soundness Γ¬φ 𝔐Γ) (soundness Γφ 𝔐Γ)
    soundness ([⊥]-elim Γ⊥) 𝔐Γ          = Logic.[⊥]-elim(soundness Γ⊥ 𝔐Γ)
    soundness {Γ = Γ}{φ = φ} ([¬]-intro Γφ⊥) 𝔐Γ 𝔐φ = soundness Γφ⊥ ([⊧₊]-strengthen {Γ₁ = Γ}{Γ₂ = singleton _} (𝔐Γ) (Logic.[↔]-to-[→] [⊧]-to-[⊧₊] 𝔐φ))
    soundness {Γ = Γ}{φ = φ} ([¬]-elim Γ¬φ⊥) {𝔐} 𝔐Γ = Logic.[¬¬]-elim {P = (𝔐 ⊧ φ)} (¬𝔐φ ↦ soundness Γ¬φ⊥ ([⊧₊]-strengthen {Γ₁ = Γ}{Γ₂ = singleton _} 𝔐Γ (Logic.[↔]-to-[→] [⊧]-to-[⊧₊] ¬𝔐φ)))
    soundness ([∧]-intro Γφ Γψ) 𝔐Γ = (Logic.[∧]-intro (soundness Γφ 𝔐Γ) (soundness Γψ 𝔐Γ))
    soundness ([∧]-elimₗ Γφψ) = Logic.[∧]-elimₗ ∘ (soundness Γφψ)
    soundness ([∧]-elimᵣ Γφψ) = Logic.[∧]-elimᵣ ∘ (soundness Γφψ)
    soundness ([∨]-introₗ Γφ) = Logic.[∨]-introₗ ∘ (soundness Γφ)
    soundness ([∨]-introᵣ Γψ) = Logic.[∨]-introᵣ ∘ (soundness Γψ)
    soundness {Γ = Γ}{φ = φ} ([∨]-elim {φ = ψ₁} {ψ₂} Γψ₁φ Γψ₂φ Γψ₁ψ₂) {𝔐} 𝔐Γ =
      (Logic.[∨]-elim
        (𝔐ψ₁ ↦ soundness Γψ₁φ ([⊧₊]-strengthen {Γ₁ = Γ}{Γ₂ = singleton _} (𝔐Γ) (Logic.[↔]-to-[→] [⊧]-to-[⊧₊] 𝔐ψ₁)))
        (𝔐ψ₂ ↦ soundness Γψ₂φ ([⊧₊]-strengthen {Γ₁ = Γ}{Γ₂ = singleton _} (𝔐Γ) (Logic.[↔]-to-[→] [⊧]-to-[⊧₊] 𝔐ψ₂)))
        (soundness Γψ₁ψ₂ 𝔐Γ)
      )
    soundness {Γ = Γ} ([⟶]-intro Γφψ) 𝔐Γ = Logic.[→]-disjunctive-formᵣ (𝔐φ ↦ soundness Γφψ ([⊧₊]-strengthen {Γ₁ = Γ}{Γ₂ = singleton _} (𝔐Γ) (Logic.[↔]-to-[→] [⊧]-to-[⊧₊] 𝔐φ)))
    soundness ([⟶]-elim Γφ Γφψ) 𝔐Γ = Logic.[→]-disjunctive-formₗ((soundness Γφψ) 𝔐Γ) (soundness Γφ 𝔐Γ)
    soundness {Γ = Γ} ([⟷]-intro {φ = φ} {ψ = ψ} Γψφ Γφψ) {𝔐} 𝔐Γ with Logic.excluded-middle(𝔐 ⊧ φ) | Logic.excluded-middle(𝔐 ⊧ ψ)
    ... | Logic.[∨]-introₗ 𝔐φ  | Logic.[∨]-introₗ 𝔐ψ  = Logic.[∨]-introₗ (Logic.[∧]-intro 𝔐φ 𝔐ψ)
    ... | Logic.[∨]-introₗ 𝔐φ  | Logic.[∨]-introᵣ ¬𝔐ψ = (Logic.[⊥]-elim ∘ ¬𝔐ψ ∘ soundness Γφψ) (Logic.[∨]-elim 𝔐Γ \{[≡]-intro → 𝔐φ})
    ... | Logic.[∨]-introᵣ ¬𝔐φ | Logic.[∨]-introₗ 𝔐ψ  = (Logic.[⊥]-elim ∘ ¬𝔐φ ∘ soundness Γψφ) (Logic.[∨]-elim 𝔐Γ \{[≡]-intro → 𝔐ψ})
    ... | Logic.[∨]-introᵣ ¬𝔐φ | Logic.[∨]-introᵣ ¬𝔐ψ = Logic.[∨]-introᵣ (Logic.[∧]-intro ¬𝔐φ ¬𝔐ψ)
    soundness {Γ = Γ} ([⟷]-elimₗ {φ = φ} {ψ = ψ} Γψ Γφψ) 𝔐Γ with soundness Γφψ 𝔐Γ
    ... | Logic.[∨]-introₗ(Logic.[∧]-intro 𝔐φ  𝔐ψ ) = 𝔐φ
    ... | Logic.[∨]-introᵣ(Logic.[∧]-intro ¬𝔐φ ¬𝔐ψ) = Logic.[⊥]-elim(¬𝔐ψ(soundness Γψ 𝔐Γ))
    soundness {Γ = Γ} ([⟷]-elimᵣ {φ = φ} {ψ = ψ} Γφ Γφψ) 𝔐Γ with soundness Γφψ 𝔐Γ
    ... | Logic.[∨]-introₗ(Logic.[∧]-intro 𝔐φ  𝔐ψ ) = 𝔐ψ
    ... | Logic.[∨]-introᵣ(Logic.[∧]-intro ¬𝔐φ ¬𝔐ψ) = Logic.[⊥]-elim(¬𝔐φ(soundness Γφ 𝔐Γ))

    satisfiable-consistent : Satisfiable(Γ) → Consistent(Γ)
    satisfiable-consistent sat = Logic.contrapositiveᵣ soundness (\p → Logic.[↔]-to-[→] [⊨]-unsatisfiability p sat)

  module _ where
    open import Data.Boolean.Stmt.Proofs
    open import Lang.Inspect

    modelSet : Model(P) → Formulas(P)
    modelSet(𝔐) = 𝔐 ⊧_

    module _ {𝔐 : Model(P)} where
      modelSet-satisfiable : Satisfiable(modelSet(𝔐))
      modelSet-satisfiable = Logic.[∃]-intro 𝔐 ⦃ id ⦄

      modelSet-maximally-consistent : MaximallyConsistent(modelSet(𝔐))
      MaximallyConsistent.consistent      modelSet-maximally-consistent = satisfiable-consistent modelSet-satisfiable
      MaximallyConsistent.element-maximal modelSet-maximally-consistent {φ} cons with TruthTable.eval 𝔐 φ | inspect (TruthTable.eval 𝔐) φ
      ... | 𝑇 | intro eval-𝑇 = TruthTable.eval-to-models {φ = φ} (Logic.[↔]-to-[←] IsTrue.is-𝑇 eval-𝑇)
      ... | 𝐹 | intro eval-𝐹 = Logic.[⊥]-elim (cons ([⊥]-intro (direct (Right [≡]-intro)) (weaken Left (direct (TruthTable.eval-to-models {φ = ¬ φ} (Logic.[↔]-to-[←] IsTrue.is-𝑇 ([≡]-with(BoolOp.¬) eval-𝐹)))))))

      {-maximally-consistent-is-modelSet : MaximallyConsistent(Γ) → (Γ ≡ₛ modelSet(𝔐))
      maximally-consistent-is-modelSet maxCon {• x} = Logic.[↔]-intro {!Logic.[↔]-to-[←] Logic.decide-is-true!} {!Logic.[↔]-to-[→] Logic.decide-is-true!}
      maximally-consistent-is-modelSet maxCon {⊤} = [⊤]-maximal-membership ⦃ maxCon ⦄
      maximally-consistent-is-modelSet maxCon {⊥} = [⊥]-maximal-membership ⦃ maxCon ⦄
      maximally-consistent-is-modelSet maxCon {¬ φ} = Logic.[↔]-transitivity ([¬]-maximal-membership ⦃ maxCon ⦄) (Logic.[¬]-unaryOperator (maximally-consistent-is-modelSet maxCon))
      maximally-consistent-is-modelSet maxCon {φ ∧ ψ} = Logic.[↔]-transitivity ([∧]-maximal-membership ⦃ maxCon ⦄) (Logic.[∧]-binaryOperator (maximally-consistent-is-modelSet maxCon) (maximally-consistent-is-modelSet maxCon))
      maximally-consistent-is-modelSet maxCon {φ ∨ ψ} = Logic.[↔]-transitivity ([∨]-maximal-membership ⦃ maxCon ⦄) (Logic.[∨]-binaryOperator (maximally-consistent-is-modelSet maxCon) (maximally-consistent-is-modelSet maxCon))
      maximally-consistent-is-modelSet maxCon {φ ⟶ ψ} = {!!}
      maximally-consistent-is-modelSet maxCon {φ ⟷ ψ} = {!!}-}

    term-model : Formulas(P){ℓ} → Model(P)
    term-model(Γ) p = Classical.decide {P = (• p) ∈ Γ} classical

  module _ ⦃ countable-P : CountablyInfinite(P) ⦄ where
    private variable Γ Γ₁ Γ₂ : Formulas(P){ℓₚ}

    term-model-of-max-proof : (con : Consistent(Γ)) → (max Γ con ≡ₛ (term-model(max Γ con) ⊧_))
    term-model-of-max-proof {Γ = Γ} con = Logic.[∃]-proof(MaximallyConsistent.equal-model-existence (max-maximally-consistent {con = con}))

    consistent-satisfiable : Consistent(Γ) → Satisfiable(Γ)
    Logic.∃.witness (consistent-satisfiable {Γ = Γ} con)     = term-model(max Γ con)
    Logic.∃.proof   (consistent-satisfiable {Γ = Γ} con) {γ} = (Logic.[↔]-to-[→] (term-model-of-max-proof {Γ = Γ} con {γ})) ∘ max-superset {con = con}

    completeness : (Γ ⊨ φ) → (Γ ⊢ φ)
    completeness {Γ = Γ}{φ = φ} =
      (Logic.[↔]-to-[←] [⊢]-deriviability-inconsistence)
      ∘ (Logic.[↔]-to-[←] Logic.contrapositive-variant2 consistent-satisfiable)
      ∘ (Logic.[↔]-to-[→] [⊨]-entailment-unsatisfiability)
-}
