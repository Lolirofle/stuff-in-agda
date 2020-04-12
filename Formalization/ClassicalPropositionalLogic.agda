open import Type
open import Logic.Classical as Logic using (Classical)
open import Logic.Predicate as Logic using ()

module Formalization.ClassicalPropositionalLogic ⦃ classical : ∀{ℓ} → Logic.∀ₗ(Classical{ℓ}) ⦄ where

import      Lvl
open import Data
open import Data.Boolean
import      Data.Boolean.Operators
open import Data.Boolean.Stmt
open import Data.Either using (Left ; Right)
private module BoolOp = Data.Boolean.Operators.Logic
open import Functional
open import Function.Names using (_⊜_)
open import Logic
open import Logic.Computability using (classicalIsComputablyDecidable)
open        Logic.Computability.ComputablyDecidable ⦃ ... ⦄ using (decide)
open import Logic.Propositional as Logic using (_←_)
open import Logic.Propositional.Theorems as Logic using ()
open import Logic.Predicate.Theorems as Logic using ()
open import Relator.Equals
open import Relator.Equals.Proofs
open import Relator.Equals.Proofs.Equivalence
open import Sets.PredicateSet using (PredSet ; _∈_ ; _∉_ ; _∪_ ; _⊆_ ; _⊇_ ; ∅ ; [≡]-to-[⊆] ; [≡]-to-[⊇]) renaming (•_ to singleton ; _≡_ to _≡ₛ_)
open        Sets.PredicateSet.BoundedQuantifiers
open import Structure.Relator.Properties
open import Syntax.Function
open import Type.Size.Countable

private variable ℓₚ ℓ ℓ₁ ℓ₂ : Lvl.Level

module _ (P : Type{ℓₚ}) where
  -- Formulas.
  -- Inductive definition of the grammatical elements of the language of propositional logic.
  data Formula : Type{ℓₚ} where
    •_ : P → Formula -- Propositional constants

    ⊤ : Formula -- Tautology (Top / True)
    ⊥ : Formula -- Contradiction (Bottom / False)

    ¬_ : Formula → Formula -- Negation (Not)

    _∧_ : Formula → Formula → Formula -- Conjunction (And)
    _∨_ : Formula → Formula → Formula -- Disjunction (Or)
    _⟶_ : Formula → Formula → Formula -- Implication
    _⟷_ : Formula → Formula → Formula -- Equivalence

  -- Double negation
  -- ¬¬_ : Formula → Formula
  -- ¬¬_ : (¬_) ∘ (¬_)

  -- Reverse implication
  _⟵_ : Formula → Formula → Formula
  _⟵_ = swap(_⟶_)

  -- (Nor)
  _⊽_ : Formula → Formula → Formula
  _⊽_ = (¬_) ∘₂ (_∨_)

  -- (Nand)
  _⊼_ : Formula → Formula → Formula
  _⊼_ = (¬_) ∘₂ (_∧_)

  -- (Exclusive or / Xor)
  _⊻_ : Formula → Formula → Formula
  _⊻_ = (¬_) ∘₂ (_⟷_)

  infixl 1011 •_
  infixl 1010 ¬_
  infixl 1005 _∧_
  infixl 1004 _∨_
  infixl 1000 _⟵_ _⟷_ _⟶_

  -- TODO: How would this thing be proven?
  -- TODO: Only if CountablyInfinite(P) or less
  instance
    Formula-is-countably-infinite : CountablyInfinite(Formula)

  -- TODO: Inline this
  Formulas : Type{ℓₚ ⊔ Lvl.𝐒(ℓ)}
  Formulas{ℓ} = PredSet{ℓ}(Formula)

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
  -- A set of formulas is valid when there is a model which satisfies all of them at the same time.
  Satisfiable : Formulas(P){ℓ} → Stmt
  Satisfiable(Γ) = Logic.∃(_⊧₊ Γ)

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
    private variable Γ : Formulas(P){ℓ}
    private variable Γ₁ : Formulas(P){ℓ₁}
    private variable Γ₂ : Formulas(P){ℓ₂}
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
    [⊧]-to-[⊧₊] = Logic.[↔]-intro (_$ [≡]-intro) (𝔐φ ↦ φγ ↦ [≡]-substitutionᵣ φγ 𝔐φ)

    [⊧]-contradiction : (𝔐 ⊧ φ) → (𝔐 ⊧ (¬ φ)) → (𝔐 ⊧ ⊥)
    [⊧]-contradiction = apply

    [⊧]-of-[¬¬] : (𝔐 ⊧ ¬(¬ φ)) → (𝔐 ⊧ φ)
    [⊧]-of-[¬¬] = Logic.[¬¬]-elim

    [⊨]-monotone : (Γ₁ ⊆ Γ₂) → ((Γ₁ ⊨_) ⊆ (Γ₂ ⊨_))
    [⊨]-monotone Γ₁Γ₂ Γ₁φ 𝔐Γ₂ = Γ₁φ (Γ₁γ ↦ 𝔐Γ₂ (Γ₁Γ₂ Γ₁γ))

    [⊨]-functionₗ : (Γ₁ ≡ₛ Γ₂) → ((Γ₁ ⊨_) ≡ₛ (Γ₂ ⊨_))
    [⊨]-functionₗ {Γ₁ = Γ₁}{Γ₂ = Γ₂} Γ₁Γ₂ {φ} = Logic.[↔]-intro ([⊨]-monotone{Γ₁ = Γ₂}{Γ₂ = Γ₁}(\{x} → [≡]-to-[⊇] (Γ₁Γ₂{x}) {x}){φ}) ([⊨]-monotone{Γ₁ = Γ₁}{Γ₂ = Γ₂}(\{x} → [≡]-to-[⊆] (Γ₁Γ₂{x}) {x}){φ})

    [⊨]-weaken : ∀{φ} → (Γ₁ ⊨ φ) → ((Γ₁ ∪ Γ₂) ⊨ φ)
    [⊨]-weaken Γ₁φ 𝔐Γ₁Γ₂ = Γ₁φ (Γ₁γ ↦ 𝔐Γ₁Γ₂ (Left Γ₁γ))

    [⊨]-validity : ∀{φ} → (∀{Γ : Formulas(P){ℓ}} → (Γ ⊨ φ)) Logic.↔ Valid(φ)
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
      r Γφψ {𝔐 = 𝔐} 𝔐Γ with Logic.excluded-middle{P = (𝔐 ⊧ φ)}
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

module TruthTable {P : Type{ℓₚ}} (decide : P → Bool) where
  eval : Formula(P) → Bool
  eval(• p)   = decide(p)
  eval(⊤)     = 𝑇
  eval(⊥)     = 𝐹
  eval(¬ φ)   = BoolOp.¬(eval(φ))
  eval(φ ∧ ψ) = eval(φ) BoolOp.∧ eval(ψ)
  eval(φ ∨ ψ) = eval(φ) BoolOp.∨ eval(ψ)
  eval(φ ⟶ ψ) = eval(φ) BoolOp.⟶ eval(ψ)
  eval(φ ⟷ ψ) = eval(φ) BoolOp.⟷ eval(ψ)

  data _⊢_ {ℓ} : Formulas(P){ℓ} → Formula(P) → Stmt{ℓₚ ⊔ Lvl.𝐒(ℓ)} where

module NaturalDeduction where
  private variable P : Type{ℓₚ}
  private variable Γ : Formulas(P){ℓₚ}
  private variable Γ₁ : Formulas(P){ℓₚ}
  private variable Γ₂ : Formulas(P){ℓₚ}
  private variable φ ψ : Formula(P)

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
    [⟷]-elimᵣ : ∀{φ ψ} → Tree(ψ) → Tree(ψ ⟷ φ) → Tree(φ)-}

  data _⊢_ {ℓₚ} {P : Type{ℓₚ}} : Formulas(P){ℓₚ} → Formula(P) → Stmt{Lvl.𝐒(ℓₚ)} where
    direct : ∀{Γ} → (Γ ⊆ (Γ ⊢_))
    weaken : ∀{Γ₁ : Formulas(P){ℓₚ}}{Γ₂ : Formulas(P){ℓₚ}}{φ} → (Γ₁ ⊢ φ) → ((Γ₁ ∪ Γ₂) ⊢ φ)

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

  {-Tree-to-[⊢]-tautologies : ∀{φ} → Tree(φ) → (∅ ⊢ φ)
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

  --[⟵]-intro : ((Γ ∪ singleton(φ)) ⊢ ψ) → (Γ ⊢ (ψ ⟵ φ))
  -- [⟵]-intro = [⟶]-intro

  -- [⟵]-elim : (Γ ⊢ φ) → (Γ ⊢ (ψ ⟵ φ)) → (Γ ⊢ ψ)
  -- [⟵]-elim = [⟶]-elim

  [¬¬]-elim : (Γ ⊢ ¬(¬ φ)) → (Γ ⊢ φ)
  [¬¬]-elim nnφ =
    ([¬]-elim
      ([⊥]-intro
        (direct(Right [≡]-intro))
        (weaken nnφ)
      )
    )

  [¬¬]-intro : (Γ ⊢ φ) → (Γ ⊢ ¬(¬ φ))
  [¬¬]-intro Γφ =
    ([¬]-intro
      ([⊥]-intro
        (weaken Γφ)
        (direct (Right [≡]-intro))
      )
    )

  _⊬_ : ∀{ℓₚ}{P : Type{ℓₚ}} → Formulas(P){ℓₚ} → Formula(P) → Stmt{Lvl.𝐒(ℓₚ)}
  _⊬_ = Logic.¬_ ∘₂ _⊢_

  [¬]-intro-converse : ((Γ ∪ singleton(φ)) ⊢ ⊥) ← (Γ ⊢ (¬ φ))
  [¬]-intro-converse {Γ = Γ}{φ = φ} Γ¬φ = [⊥]-intro (direct (Right [≡]-intro)) (weaken Γ¬φ)

  Inconsistent : Formulas(P) → Stmt
  Inconsistent(Γ) = Γ ⊢ ⊥

  Consistent : Formulas(P) → Stmt
  Consistent(Γ) = Γ ⊬ ⊥ 

  consistency-of-[∪]ₗ : ∀{Γ₁ : Formulas{ℓ}(P)}{Γ₂} → Consistent(Γ₁ ∪ Γ₂) → Consistent(Γ₁)
  consistency-of-[∪]ₗ con z = con (weaken z)

  [⊢]-deriviability-inconsistence : (Γ ⊢ φ) Logic.↔ Inconsistent(Γ ∪ singleton(¬ φ))
  [⊢]-deriviability-inconsistence {Γ}{φ} = Logic.[↔]-intro [¬]-elim ([¬]-intro-converse ∘ [¬¬]-intro)

  [⊢]-explosion-inconsistence : (∀{φ} → (Γ ⊢ φ)) Logic.↔ Inconsistent(Γ)
  [⊢]-explosion-inconsistence {Γ} = Logic.[↔]-intro (λ z → [⊥]-elim z) (λ z → z)

  -- TODO: Unprovable unless Γ₂ is finite?
  -- [⊢]-monotone : (Γ₁ ⊆ Γ₂) → ((Γ₁ ⊢_) ⊆ (Γ₂ ⊢_))
  -- [⊢]-monotone {Γ₁}{Γ₂} Γ₁Γ₂ {φ} Γ₁φ = {!!} -- weaken Γ₁φ {Γ₂}

  -- TODO: Uses [⊢]-monotone, which is unproven
  -- [⊢]-functionₗ : (Γ₁ ≡ₛ Γ₂) → ((Γ₁ ⊢_) ≡ₛ (Γ₂ ⊢_))
  -- [⊢]-functionₗ Γ₁Γ₂ = Logic.[↔]-intro ([⊢]-monotone (Logic.[↔]-to-[←] Γ₁Γ₂)) ([⊢]-monotone (Logic.[↔]-to-[→] Γ₁Γ₂))

  [⊢]-compose : (Γ ⊢ φ) → ((Γ ∪ singleton(φ)) ⊢ ψ) → (Γ ⊢ ψ)
  [⊢]-compose Γφ Γφψ = [∨]-elim Γφψ Γφψ ([∨]-introₗ Γφ)

  [⊢]-compose-inconsistence : (Γ ⊢ φ) → ((Γ ∪ singleton(φ)) ⊢ ⊥) → Inconsistent(Γ)
  [⊢]-compose-inconsistence Γφ Γφ⊥ = [⊥]-intro Γφ ([¬]-intro Γφ⊥)

  -- TODO: Is this provable? Does one need to include it in the definition of (_⊢_)? Is it even possible to include it?
  -- [⊢]-hypothesis : ((Γ ⊢ φ) → (Γ ⊢ ψ)) → ((Γ ∪ singleton(φ)) ⊢ ψ)
  -- [⊢]-hypothesis hyp = {!!}

  [⊢][→]-intro-from-[∨] : (Γ ⊢ ¬ φ) Logic.∨ (Γ ⊢ ψ) → (Γ ⊢ (φ ⟶ ψ))
  [⊢][→]-intro-from-[∨] {Γ = Γ}{φ}{ψ} (Left x) = [⟶]-intro ([⊥]-elim ([⊥]-intro (direct (Right [≡]-intro)) (weaken {Γ₂ = singleton φ} x)))
  [⊢][→]-intro-from-[∨] (Right x) = [⟶]-intro (weaken x)

  record MaximallyConsistent {P : Type{ℓₚ}} (Γ : Formulas(P)) : Stmt{Lvl.𝐒(ℓₚ)} where
    field
      consistent : Consistent(Γ)
      maximal    : ∀{Δ : Formulas(P)} → Consistent(Γ ∪ Δ) → (Δ ⊆ Γ)

    element-maximal : ∀{φ} → Consistent(Γ ∪ singleton(φ)) → (φ ∈ Γ)
    element-maximal con = maximal con [≡]-intro

    element-maximal-contra : ∀{φ} → (φ ∉ Γ) → Inconsistent(Γ ∪ singleton(φ))
    element-maximal-contra = Logic.contrapositive-variantₗ element-maximal

    [⊢]-to-[∈] : ∀{φ} → (Γ ⊢ φ) → (φ ∈ Γ)
    [⊢]-to-[∈] = Logic.[→]-from-contrary (λ Γφ φ∉Γ → consistent ([⊢]-compose-inconsistence Γφ (element-maximal-contra φ∉Γ)))

    -- excluded-middle-formula-membership : ∀{φ} → (φ ∈ Γ) Logic.∨ ((¬ φ) ∈ Γ)

    [∧]-formula-membership : ∀{φ ψ} → ((φ ∧ ψ) ∈ Γ) Logic.↔ ((φ ∈ Γ) Logic.∧ (ψ ∈ Γ))
    [∧]-formula-membership {φ}{ψ} = Logic.[↔]-intro l r where
      l : ((φ ∧ ψ) ∈ Γ) ← ((φ ∈ Γ) Logic.∧ (ψ ∈ Γ))
      l (Logic.[∧]-intro φΓ ψΓ) = [⊢]-to-[∈] ([∧]-intro (direct φΓ) (direct ψΓ))

      r : ((φ ∧ ψ) ∈ Γ) → ((φ ∈ Γ) Logic.∧ (ψ ∈ Γ))
      r φψΓ = Logic.[∧]-intro ([⊢]-to-[∈] ([∧]-elimₗ(direct φψΓ))) ([⊢]-to-[∈] ([∧]-elimᵣ(direct φψΓ)))

    [∨]-formula-membership : ∀{φ ψ} → ((φ ∨ ψ) ∈ Γ) Logic.↔ ((φ ∈ Γ) Logic.∨ (ψ ∈ Γ))
    [∨]-formula-membership {φ}{ψ} = Logic.[↔]-intro l r where
      l : ((φ ∨ ψ) ∈ Γ) ← ((φ ∈ Γ) Logic.∨ (ψ ∈ Γ))
      l = Logic.[∨]-elim ([⊢]-to-[∈] ∘ [∨]-introₗ ∘ direct) ([⊢]-to-[∈] ∘ [∨]-introᵣ ∘ direct)

      r : ((φ ∨ ψ) ∈ Γ) → ((φ ∈ Γ) Logic.∨ (ψ ∈ Γ))
      r = Logic.contrapositiveₗ ⦃ classical ⦄ ((\{(Logic.[∧]-intro ¬φΓ ¬ψΓ) → φψΓ ↦ consistent([∨]-elim (element-maximal-contra ¬φΓ) (element-maximal-contra ¬ψΓ) (direct φψΓ))}) ∘ Logic.[↔]-to-[←] Logic.[¬][∨])

    -- [⟶]-formula-membership : ∀{φ ψ} → ((φ ⟶ ψ) ∈ Γ) Logic.↔ ((φ ∉ Γ) Logic.∨ (ψ ∈ Γ))
    -- [⟶]-formula-membership {φ}{ψ} = Logic.[↔]-intro l r where
      -- l : ((φ ⟶ ψ) ∈ Γ) ← ((φ ∉ Γ) Logic.∨ (ψ ∈ Γ))
      -- r : ((φ ⟶ ψ) ∈ Γ) → ((φ ∉ Γ) Logic.∨ (ψ ∈ Γ))

  -- Also called: Lindenbaums' lemma
  max : (Γ : Formulas(P)) → Consistent(Γ) → Formulas(P)
  max Γ con φ = Consistent(Γ ∪ singleton(φ))

  max-maximally-consistent : ∀{con : Consistent(Γ)} → MaximallyConsistent(max Γ con)

  max-superset : ∀{con : Consistent(Γ)} → (Γ ⊆ max Γ con)
  max-superset {con = con} {x = φ} φΓ Γφ⊥ = con ([⊥]-intro (direct φΓ) ([¬]-intro Γφ⊥))

module _ where
  open Semantics
  open Semantics.Proofs
  open NaturalDeduction

  private variable P : Type{ℓₚ}
  private variable Γ Γ₁ Γ₂ : Formulas(P){ℓₚ}
  private variable φ ψ : Formula(P)

  soundness : (Γ ⊢ φ) → (Γ ⊨ φ)
  soundness (direct Γφ) 𝔐Γ            = 𝔐Γ(Γφ)
  soundness (weaken {Γ₁}{Γ₂}{φ} Γ₁φ)  = [⊨]-weaken {Γ₁ = Γ₁}{Γ₂ = Γ₂}{φ} (soundness Γ₁φ) 
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
  soundness {Γ = Γ} ([⟷]-intro {φ = φ} {ψ = ψ} Γψφ Γφψ) {𝔐} 𝔐Γ with Logic.excluded-middle{P = 𝔐 ⊧ φ} | Logic.excluded-middle{P = 𝔐 ⊧ ψ}
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

  term-model : Formulas(P){ℓ} → Model(P)
  term-model(Γ) p = Classical.decide {P = (• p) ∈ Γ} classical

  term-model-of-max-proof : (con : Consistent(Γ)) → (term-model(max Γ con) ⊧ φ) Logic.↔ (φ ∈ max Γ con)
  term-model-of-max-proof {Γ = Γ}{φ = φ} con = Logic.[↔]-intro l r where
    l : (term-model(max Γ con) ⊧ φ) ← (φ ∈ max Γ con)
    l φmax = {!!}
    r : (term-model(max Γ con) ⊧ φ) → (φ ∈ max Γ con)
    r modelsφ Γφ-incons = {![¬]-intro Γφ-incons!}
    -- (term-model (max Γ con) ⊧ φ) → (Γ ⊢ φ) ? Or maybe (max Γ con ⊢ φ)?

  consistent-satisfiable : Consistent(Γ) → Satisfiable(Γ)
  Logic.∃.witness (consistent-satisfiable {Γ = Γ} con)     = term-model(max Γ con)
  Logic.∃.proof   (consistent-satisfiable {Γ = Γ} con) {γ} = (Logic.[↔]-to-[←] (term-model-of-max-proof {Γ = Γ}{φ = γ} con)) ∘ max-superset {con = con}

  completeness : (Γ ⊨ φ) → (Γ ⊢ φ)
  completeness {Γ = Γ}{φ = φ} =
    (Logic.[↔]-to-[←] [⊢]-deriviability-inconsistence)
    ∘ (Logic.contrapositive-variantₗ consistent-satisfiable)
    ∘ (Logic.[↔]-to-[→] [⊨]-entailment-unsatisfiability)
