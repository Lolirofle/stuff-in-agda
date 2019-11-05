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
open import Functional.Names using (_⊜_)
open import Logic
open import Logic.Computability using (classicalIsComputablyDecidable)
open        Logic.Computability.ComputablyDecidable ⦃ ... ⦄ using (decide)
open import Logic.Propositional as Logic using ()
open import Logic.Propositional.Theorems as Logic using ()
open import Relator.Equals
open import Relator.Equals.Proofs
open import Relator.Equals.Proofs.Equivalence
open import Sets.PredicateSet using (_∈_ ; _∉_ ; _∪_ ; _⊆_ ; _⊇_ ; ∅ ; [≡]-to-[⊆] ; [≡]-to-[⊇]) renaming (•_ to singleton ; _≡_ to _≡ₛ_)
open import Structure.Relator.Properties
open import Syntax.Function
open import Type.Size.Countable

private variable ℓₚ ℓ ℓ₁ ℓ₂ : Lvl.Level

module _ (P : Type{ℓₚ}) where
  data Formula : Type{ℓₚ} where
    •_ : P → Formula

    ⊤ : Formula
    ⊥ : Formula

    ¬_ : Formula → Formula

    _∧_ : Formula → Formula → Formula
    _∨_ : Formula → Formula → Formula
    _⟶_ : Formula → Formula → Formula
    _⟷_ : Formula → Formula → Formula

  _⟵_ : Formula → Formula → Formula
  _⟵_ = swap(_⟶_)

  infixl 1011 •_
  infixl 1010 ¬_
  infixl 1005 _∧_
  infixl 1004 _∨_
  infixl 1000 _⟵_ _⟷_ _⟶_

  -- TODO: How would this thing be proven?
  instance
    Formula-is-countably-infinite : CountablyInfinite(Formula)

  Formulas : Type{ℓₚ ⊔ Lvl.𝐒(ℓ)}
  Formulas{ℓ} = Formula → Stmt{ℓ}

module Semantics where
  private variable P : Type{ℓₚ}

  Model : Type{ℓₚ} → Type{ℓₚ}
  Model(P) = (P → Bool)

  -- Satisfication relation.
  -- (𝔐 ⊧ φ) means that the formula φ is satisfied in the model 𝔐.
  _⊧_ : Model(P) → Formula(P) → Stmt
  𝔐 ⊧ (• p)   = IsTrue(𝔐(p))
  𝔐 ⊧ ⊤       = Logic.⊤
  𝔐 ⊧ ⊥       = Logic.⊥
  𝔐 ⊧ (¬ φ)   = Logic.¬(𝔐 ⊧ φ)
  𝔐 ⊧ (φ ∧ ψ) = (𝔐 ⊧ φ) Logic.∧ (𝔐 ⊧ ψ)
  𝔐 ⊧ (φ ∨ ψ) = (𝔐 ⊧ φ) Logic.∨ (𝔐 ⊧ ψ)
  𝔐 ⊧ (φ ⟶ ψ) = Logic.¬(𝔐 ⊧ φ) Logic.∨ (𝔐 ⊧ ψ)
  𝔐 ⊧ (φ ⟷ ψ) = ((𝔐 ⊧ φ) Logic.∧ (𝔐 ⊧ ψ)) Logic.∨ (Logic.¬(𝔐 ⊧ φ) Logic.∧ Logic.¬(𝔐 ⊧ ψ))

  -- Satisfication of a set of formulas.
  -- This means that a model satisfies all formulas at the same time.
  _⊧₊_ : Model(P) → Formulas(P){ℓ} → Stmt
  𝔐 ⊧₊ Γ = (∀{γ} → Γ(γ) → (𝔐 ⊧ γ))

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

    [⊧]-to-[⊧₊] : (𝔐 ⊧ φ) → (𝔐 ⊧₊ singleton(φ))
    [⊧]-to-[⊧₊] 𝔐φ φγ = [≡]-substitutionᵣ φγ 𝔐φ

    [⊨]-monotone : (Γ₁ ⊆ Γ₂) → ((Γ₁ ⊨_) ⊆ (Γ₂ ⊨_))
    [⊨]-monotone Γ₁Γ₂ Γ₁φ 𝔐Γ₂ = Γ₁φ (Γ₁γ ↦ 𝔐Γ₂ (Γ₁Γ₂ Γ₁γ))

    [⊨]-functionₗ : (Γ₁ ≡ₛ Γ₂) → ((Γ₁ ⊨_) ≡ₛ (Γ₂ ⊨_))
    [⊨]-functionₗ {Γ₁ = Γ₁}{Γ₂ = Γ₂} Γ₁Γ₂ {φ} = Logic.[↔]-intro ([⊨]-monotone{Γ₁ = Γ₂}{Γ₂ = Γ₁}(\{x} → [≡]-to-[⊇] (Γ₁Γ₂{x}) {x}){φ}) ([⊨]-monotone{Γ₁ = Γ₁}{Γ₂ = Γ₂}(\{x} → [≡]-to-[⊆] (Γ₁Γ₂{x}) {x}){φ})

    [⊨]-weaken : ∀{φ} → (Γ₁ ⊨ φ) → ((Γ₁ ∪ Γ₂) ⊨ φ)
    [⊨]-weaken Γ₁φ 𝔐Γ₁Γ₂ = Γ₁φ (Γ₁γ ↦ 𝔐Γ₁Γ₂ (Left Γ₁γ))

    [⊨]-validity : ∀{φ} → (∀{Γ : Formulas(P){ℓ}} → (Γ ⊨ φ)) Logic.↔ Valid(φ)
    [⊨]-validity = Logic.[↔]-intro (λ r → const r) (λ l → l{∅} empty)

    [⊨]-entailment-unsatisfiability : (Γ ⊨ φ) Logic.↔ Unsatisfiable(Γ ∪ singleton(¬ φ))
    [⊨]-entailment-unsatisfiability {Γ = Γ}{φ = φ} = Logic.[↔]-intro (λ r {𝔐} 𝔐Γ → Logic.[⊥]-elim (r (Logic.[∃]-intro 𝔐 ⦃ λ x → 𝔐Γ (Logic.[∨]-elim id (λ x₁ → {!!}) x) ⦄))) λ{l (Logic.[∃]-intro 𝔐 ⦃ sat ⦄) → {!sat!}}

    [⊨][⟶]-intro : ((Γ ∪ singleton(φ)) ⊨ ψ) Logic.↔ (Γ ⊨ (φ ⟶ ψ))
    [⊨]-unsatisfiability : (Γ ⊨ ⊥) Logic.↔ Unsatisfiable(Γ)
    [⊨][¬]-intro : ((Γ ∪ singleton(φ)) ⊨ ⊥) Logic.↔ (Γ ⊨ (¬ φ))

module TruthTable {P : Type{ℓₚ}} (decide : P → Bool) where
  eval : Formula(P) → Bool
  eval(• p)   = decide(p)
  eval(⊤)     = 𝑇
  eval(⊥)     = 𝐹
  eval(¬ φ)   = BoolOp.¬ eval(φ)
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

    [⟷]-intro : ∀{Γ}{φ ψ} → ((Γ ∪ singleton(ψ)) ⊢ φ) → ((Γ ∪ singleton(φ)) ⊢ ψ) → (Γ ⊢ (ψ ⟷ φ))
    [⟷]-elimₗ : ∀{Γ}{φ ψ} → (Γ ⊢ φ) → (Γ ⊢ (ψ ⟷ φ)) → (Γ ⊢ ψ)
    [⟷]-elimᵣ : ∀{Γ}{φ ψ} → (Γ ⊢ ψ) → (Γ ⊢ (ψ ⟷ φ)) → (Γ ⊢ φ)

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

  consistency-of-[∪]ₗ : ∀{Γ₁ : Formulas(P)}{Γ₂} → Consistent(Γ₁ ∪ Γ₂) → Consistent(Γ₁)
  consistency-of-[∪]ₗ con z = con (weaken z)

  [⊢]-deriviability-inconsistence : (Γ ⊢ φ) Logic.↔ Inconsistent(Γ ∪ singleton(¬ φ))
  [⊢]-deriviability-inconsistence {Γ}{φ} = Logic.[↔]-intro [¬]-elim ([¬]-intro-converse ∘ [¬¬]-intro)

  [⊢]-explosion-inconsistence : (∀{φ} → (Γ ⊢ φ)) Logic.↔ Inconsistent(Γ)
  [⊢]-explosion-inconsistence {Γ} = Logic.[↔]-intro (λ z → [⊥]-elim z) (λ z → z)

  -- TODO: Unprovable unless Γ₂ is finite?
  [⊢]-monotone : (Γ₁ ⊆ Γ₂) → ((Γ₁ ⊢_) ⊆ (Γ₂ ⊢_))
  -- [⊢]-monotone {Γ₁}{Γ₂} Γ₁Γ₂ {φ} Γ₁φ = {!!} -- weaken Γ₁φ {Γ₂}

  [⊢]-functionₗ : (Γ₁ ≡ₛ Γ₂) → ((Γ₁ ⊢_) ≡ₛ (Γ₂ ⊢_))
  [⊢]-functionₗ Γ₁Γ₂ = Logic.[↔]-intro ([⊢]-monotone (Logic.[↔]-to-[←] Γ₁Γ₂)) ([⊢]-monotone (Logic.[↔]-to-[→] Γ₁Γ₂))

  [⊢]-compose : (Γ ⊢ φ) → ((Γ ∪ singleton(φ)) ⊢ ψ) → (Γ ⊢ ψ)
  [⊢]-compose Γφ Γφψ = [∨]-elim Γφψ Γφψ ([∨]-introₗ Γφ)

  [⊢]-compose-inconsistence : (Γ ⊢ φ) → ((Γ ∪ singleton(φ)) ⊢ ⊥) → Inconsistent(Γ)
  [⊢]-compose-inconsistence Γφ Γφ⊥ = [⊥]-intro Γφ ([¬]-intro Γφ⊥)

  -- TODO: Is this provable? Does one need to include it in the definition of (_⊢_)? Is it even possible to include it?
  [⊢]-hypothesis : ((Γ ⊢ φ) → (Γ ⊢ ψ)) → ((Γ ∪ singleton(φ)) ⊢ ψ)
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

    excluded-middle-formula-inclusion : ∀{φ} → (φ ∈ Γ) Logic.∨ ((¬ φ) ∈ Γ)

    [∧]-formula-inclusion : ∀{φ ψ} → ((φ ∧ ψ) ∈ Γ) Logic.↔ ((φ ∈ Γ) Logic.∧ (ψ ∈ Γ))

    [∨]-formula-inclusion : ∀{φ ψ} → ((φ ∨ ψ) ∈ Γ) Logic.↔ ((φ ∈ Γ) Logic.∨ (ψ ∈ Γ))

    [⟶]-formula-inclusion : ∀{φ ψ} → ((φ ⟶ ψ) ∈ Γ) Logic.↔ ((φ ∉ Γ) Logic.∨ (ψ ∈ Γ))

  -- Also called: Lindenbaums' lemma
  max : (Γ : Formulas(P){ℓₚ}) → Consistent(Γ) → Formulas(P){Lvl.𝐒(ℓₚ)}
  max Γ con φ = {!Consistent(Γ ∪ singleton(φ))!}

  max-maximally-consistent : (con : Consistent(Γ)) → MaximallyConsistent(max Γ con)
  max-superset : (con : Consistent(Γ)) → (Γ ⊆ max Γ con)

module _ where
  open Semantics
  open Semantics.Proofs
  open NaturalDeduction

  private variable P : Type{ℓₚ}
  private variable Γ : Formulas(P){ℓₚ}
  private variable Γ₁ : Formulas(P){ℓₚ}
  private variable Γ₂ : Formulas(P){ℓₚ}
  private variable φ ψ : Formula(P)

  soundness : (Γ ⊢ φ) → (Γ ⊨ φ)
  soundness (direct Γφ) 𝔐Γ            = 𝔐Γ(Γφ)
  soundness (weaken {Γ₁}{Γ₂}{φ} Γ₁φ)  = [⊨]-weaken {Γ₁ = Γ₁}{Γ₂ = Γ₂}{φ} (soundness Γ₁φ) 
  soundness [⊤]-intro                 = const(Logic.[⊤]-intro)
  soundness ([⊥]-intro Γφ Γ¬φ) 𝔐Γ     = (soundness Γ¬φ 𝔐Γ) (soundness Γφ 𝔐Γ)
  soundness ([⊥]-elim Γ⊥) 𝔐Γ          = Logic.[⊥]-elim(soundness Γ⊥ 𝔐Γ)
  soundness {Γ = Γ}{φ = φ} ([¬]-intro Γφ⊥) 𝔐Γ 𝔐φ = soundness Γφ⊥ ([⊧₊]-strengthen {Γ₁ = Γ}{Γ₂ = singleton _} (𝔐Γ) ([⊧]-to-[⊧₊] 𝔐φ))
  soundness {Γ = Γ}{φ = φ} ([¬]-elim Γ¬φ⊥) {𝔐} 𝔐Γ = Logic.[¬¬]-elim {P = (𝔐 ⊧ φ)} (¬𝔐φ ↦ soundness Γ¬φ⊥ ([⊧₊]-strengthen {Γ₁ = Γ}{Γ₂ = singleton _} 𝔐Γ ([⊧]-to-[⊧₊] ¬𝔐φ)))
  soundness ([∧]-intro Γφ Γψ) 𝔐Γ =
    (Logic.[∧]-intro
      (soundness Γφ 𝔐Γ)
      (soundness Γψ 𝔐Γ)
    )
  soundness ([∧]-elimₗ Γφψ) = Logic.[∧]-elimₗ ∘ (soundness Γφψ)
  soundness ([∧]-elimᵣ Γφψ) = Logic.[∧]-elimᵣ ∘ (soundness Γφψ)
  soundness ([∨]-introₗ Γφ) = Logic.[∨]-introₗ ∘ (soundness Γφ)
  soundness ([∨]-introᵣ Γψ) = Logic.[∨]-introᵣ ∘ (soundness Γψ)
  soundness {Γ = Γ}{φ = φ} ([∨]-elim {φ = ψ₁} {ψ₂} Γψ₁φ Γψ₂φ Γψ₁ψ₂) {𝔐} 𝔐Γ =
    (Logic.[∨]-elim
      (𝔐ψ₁ ↦ soundness Γψ₁φ ([⊧₊]-strengthen {Γ₁ = Γ}{Γ₂ = singleton _} (𝔐Γ) ([⊧]-to-[⊧₊] 𝔐ψ₁)))
      (𝔐ψ₂ ↦ soundness Γψ₂φ ([⊧₊]-strengthen {Γ₁ = Γ}{Γ₂ = singleton _} (𝔐Γ) ([⊧]-to-[⊧₊] 𝔐ψ₂)))
      (soundness Γψ₁ψ₂ 𝔐Γ)
    )
  soundness {Γ = Γ}{φ = φ} ([⟶]-intro Γφψ) 𝔐Γ = Logic.[→]-disjunctive-formᵣ (𝔐φ ↦ soundness Γφψ ([⊧₊]-strengthen {Γ₁ = Γ}{Γ₂ = singleton _} (𝔐Γ) ([⊧]-to-[⊧₊] 𝔐φ)))
  soundness ([⟶]-elim Γφ Γφψ) 𝔐Γ = Logic.[→]-disjunctive-formₗ((soundness Γφψ) 𝔐Γ) (soundness Γφ 𝔐Γ)
  soundness ([⟷]-intro x x₁) 𝔐Γ = {!!}
  soundness ([⟷]-elimₗ x x₁) 𝔐Γ = {!!}
  soundness ([⟷]-elimᵣ x x₁) 𝔐Γ = {!!}

  -- TODO: term-model = id -- Essentially means that (P = Formula)?
  term-model : Formulas(P){ℓ} → Model(P)
  term-model(Γ) p = decide ⦃ Logic.[↔]-to-[→] classicalIsComputablyDecidable classical ⦄ (Γ(• p))

  term-model-of-max-proof : (con : Consistent(Γ)) → (term-model(max Γ con) ⊧ φ) Logic.↔ (φ ∈ max Γ con)

  consistent-satisfiable : Consistent(Γ) → Satisfiable(Γ)
  Logic.∃.witness (consistent-satisfiable {Γ = Γ} con)     = term-model(max Γ con)
  Logic.∃.proof   (consistent-satisfiable {Γ = Γ} con) {γ} = (Logic.[↔]-to-[←] (term-model-of-max-proof {Γ = Γ}{φ = γ} con)) ∘ (max-superset con)

  completeness : (Γ ⊨ φ) → (Γ ⊢ φ)
  completeness {Γ = Γ}{φ = φ} =
    (Logic.[↔]-to-[←] [⊢]-deriviability-inconsistence)
    ∘ (Logic.contrapositive-variantₗ consistent-satisfiable)
    ∘ (Logic.[↔]-to-[→] [⊨]-entailment-unsatisfiability)
