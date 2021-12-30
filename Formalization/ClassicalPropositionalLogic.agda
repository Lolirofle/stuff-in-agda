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
open import Structure.Function
open import Structure.Relator.Properties
open import Syntax.Function
open import Type.Properties.Decidable.Proofs
open import Type.Properties.Decidable
open import Type.Size.Countable

private variable ℓₚ ℓ ℓ₁ ℓ₂ : Lvl.Level

open import Formalization.ClassicalPropositionalLogic.NaturalDeduction
open import Formalization.ClassicalPropositionalLogic.NaturalDeduction.Proofs
open import Formalization.ClassicalPropositionalLogic.Syntax
open import Formalization.ClassicalPropositionalLogic.Syntax.Proofs
open import Formalization.ClassicalPropositionalLogic.Semantics
open import Formalization.ClassicalPropositionalLogic.Semantics.Proofs
import      Formalization.ClassicalPropositionalLogic.TruthTable as TruthTable

instance _ = classical-to-decidable
instance _ = classical-to-decider

module NaturalDeduction where
  private variable P : Type{ℓₚ}
  private variable Γ Γ₁ Γ₂ : Formulas(P){ℓ}
  private variable φ ψ : Formula(P)

  [⊢]-functionₗ : (Γ₁ ≡ₛ Γ₂) → ((Γ₁ ⊢_) ≡ₛ (Γ₂ ⊢_))
  [⊢]-functionₗ Γ₁Γ₂ = Logic.[↔]-intro (weaken (Logic.[↔]-to-[←] Γ₁Γ₂)) (weaken (Logic.[↔]-to-[→] Γ₁Γ₂))

  [⊢]-compose : (Γ ⊢ φ) → ((Γ ∪ singleton(φ)) ⊢ ψ) → (Γ ⊢ ψ)
  [⊢]-compose Γφ Γφψ = [∨]-elim Γφψ Γφψ ([∨]-introₗ Γφ)

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
    postulate sl : (finiteAssumptions p ∪ singleton(φ)) ⊆ ((((finiteAssumptions p ∖ singleton(φ)) ∪ (finiteAssumptions q ∖ singleton(ψ))) ∪ finiteAssumptions r) ∪ singleton(φ))
    postulate sr : (finiteAssumptions q ∪ singleton(ψ)) ⊆ ((((finiteAssumptions p ∖ singleton(φ)) ∪ (finiteAssumptions q ∖ singleton(ψ))) ∪ finiteAssumptions r) ∪ singleton(ψ))
  finiteAssumptions-correctness ([⟶]-intro  p)     = [⟶]-intro (weaken (Logic.[↔]-to-[←] ([∖][∪]-is-[∪] {A = finiteAssumptions p}{B = singleton _}) ∘ Logic.[∨]-introₗ) (finiteAssumptions-correctness p))
  finiteAssumptions-correctness ([⟶]-elim   p q)   = [⟶]-elim (weaken Left (finiteAssumptions-correctness p)) (weaken Right (finiteAssumptions-correctness q))
  finiteAssumptions-correctness ([⟷]-intro  p q)   = [⟷]-intro (weaken (sl ∘ Left) (finiteAssumptions-correctness p)) (weaken (sr ∘ Left) (finiteAssumptions-correctness q)) where
    postulate sl : (finiteAssumptions p ∪ singleton(φ)) ⊆ (((finiteAssumptions p ∖ singleton(φ)) ∪ (finiteAssumptions q ∖ singleton(ψ))) ∪ singleton(φ))
    postulate sr : (finiteAssumptions q ∪ singleton(ψ)) ⊆ (((finiteAssumptions p ∖ singleton(φ)) ∪ (finiteAssumptions q ∖ singleton(ψ))) ∪ singleton(ψ))
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

  module _ (Γ : Formulas(P){ℓ}) where
    ConsistentSubsetMaximality  = ∀{Δ : Formulas(P){Lvl.of(P) Lvl.⊔ ℓ}} → Consistent(Δ) → (Γ ⊆ Δ) → (Δ ⊆ Γ)
    ConsistentElementMaximality = ∀{φ} → Consistent(Γ ∪ singleton(φ)) → (φ ∈ Γ)
    CompleteDerivability        = ∀{φ} → (Γ ⊢ φ) Logic.∨ (Γ ⊢ (¬ φ))
    CompleteMembership          = ∀{φ} → (φ ∈ Γ) Logic.∨ ((¬ φ) ∈ Γ)

    -- Equivalences when `Γ` is consistent. Used in the definition of `MaximallyConsistent`.
    data ConsistentlyComplete : Stmt{Lvl.𝐒(Lvl.of(P) Lvl.⊔ ℓ)} where
      subset-intro          : ConsistentSubsetMaximality  → ConsistentlyComplete
      element-intro         : ConsistentElementMaximality → ConsistentlyComplete
      complete-deriv-intro  : CompleteDerivability        → ConsistentlyComplete
      complete-member-intro : CompleteMembership          → ConsistentlyComplete

    module CompleteMembership(p : CompleteMembership) where
      consistentSubsetMaximality : ConsistentSubsetMaximality
      consistentSubsetMaximality conΔ ΓΔ {φ} φΔ = Logic.[∨]-not-right (p{φ}) (¬φΓ ↦ conΔ([⊥]-intro (direct φΔ) (direct(ΓΔ ¬φΓ))))

    module ConsistentElementMaximality(element-maximal : ConsistentElementMaximality) where
      consistentSubsetMaximality : ConsistentSubsetMaximality
      consistentSubsetMaximality conΔ ΓΔ {φ} φΔ = element-maximal ([⊢]-subset-consistency (Logic.[∨]-elim ΓΔ (\{([≡]-intro) → φΔ})) conΔ)

      element-maximal-contra : (φ ∉ Γ) → Inconsistent(Γ ∪ singleton(φ))
      element-maximal-contra = Logic.[↔]-to-[←] Logic.contrapositive-variant2 element-maximal

      [⊢]-derivability-consistencyₗ : ((Γ ⊢ φ) ← Consistent(Γ ∪ singleton(φ)))
      [⊢]-derivability-consistencyₗ = direct ∘ element-maximal

      module Consistent(consistent : Consistent(Γ)) where
        [⊢]-to-[∈] : (Γ ⊢ φ) → (φ ∈ Γ)
        [⊢]-to-[∈] = Logic.[→]-from-contrary (\Γφ φ∉Γ → consistent ([⊢]-compose-inconsistency Γφ (element-maximal-contra φ∉Γ)))

        [⊢][∈]-equivalence : (Γ ⊢ φ) Logic.↔ (φ ∈ Γ)
        [⊢][∈]-equivalence = Logic.[↔]-intro direct [⊢]-to-[∈]

        -- [•]-maximal-membership : ((• p) ∈ Γ) Logic.↔ ?
        -- [•]-maximal-membership = 

        [⊤]-maximal-membership : (⊤ ∈ Γ) Logic.↔ Logic.⊤
        [⊤]-maximal-membership = Logic.[↔]-intro l r where
          l = const (element-maximal (Γ⊤-incons ↦ consistent([⊢]-compose-inconsistency [⊤]-intro Γ⊤-incons)))
          r = const Logic.[⊤]-intro

        [⊥]-maximal-membership : (⊥ ∈ Γ) Logic.↔ Logic.⊥
        [⊥]-maximal-membership = Logic.[↔]-intro l r where
          l = Logic.[⊥]-elim
          r = consistent ∘ direct

        [¬]-maximal-membership : ((¬ φ) ∈ Γ) Logic.↔ (φ ∉ Γ)
        [¬]-maximal-membership = Logic.[↔]-intro l r where
          l = [⊢]-to-[∈] ∘ [¬]-intro ∘ element-maximal-contra
          r = [⊢]-consistent-noncontradicting-membership consistent

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
            (Either.map (Logic.[↔]-to-[←] [∧]-maximal-membership) (Logic.[↔]-to-[←] [∧]-maximal-membership))
            (Either.map (Logic.[↔]-to-[→] [∧]-maximal-membership) (Logic.[↔]-to-[→] [∧]-maximal-membership))
                                                ⦗ Logic.[↔]-transitivity ⦘ₗ
          Logic.[↔]-intro
            (Either.mapRight (Tuple.map (Logic.[↔]-to-[←] [¬]-maximal-membership) (Logic.[↔]-to-[←] [¬]-maximal-membership)))
            (Either.mapRight (Tuple.map (Logic.[↔]-to-[→] [¬]-maximal-membership) (Logic.[↔]-to-[→] [¬]-maximal-membership)))

        complete-membership : CompleteMembership
        complete-membership = Logic.[¬→]-disjunctive-formᵣ (Logic.[↔]-to-[←] [¬]-maximal-membership)

        equal-model-existence : Logic.∃(𝔐 ↦ (Γ ≡ₛ (𝔐 ⊧_)))
        equal-model-existence = Logic.[∃]-intro witness ⦃ Logic.[↔]-intro l r ⦄ where
          witness = (p ↦ decide(0)((• p) ∈ Γ))

          l : (witness ⊧ φ) → (φ ∈ Γ)
          r : witness ⊧₊ Γ

          r {• x}   = Logic.[↔]-to-[→] decider-true
          r {⊤}     = Logic.[↔]-to-[→] [⊤]-maximal-membership
          r {⊥}     = Logic.[↔]-to-[→] [⊥]-maximal-membership
          r {¬ φ}   = Logic.contrapositiveᵣ l ∘ Logic.[↔]-to-[→] [¬]-maximal-membership
          r {φ ∧ ψ} = Tuple.map r r ∘ Logic.[↔]-to-[→] [∧]-maximal-membership
          r {φ ∨ ψ} = Either.map r r ∘ Logic.[↔]-to-[→] [∨]-maximal-membership
          r {φ ⟶ ψ} = Either.map (Logic.contrapositiveᵣ l) r ∘ Logic.[↔]-to-[→] [⟶]-maximal-membership
          r {φ ⟷ ψ} = Either.map (Tuple.map r r) (Tuple.map (Logic.contrapositiveᵣ l) (Logic.contrapositiveᵣ l)) ∘ Logic.[↔]-to-[→] [⟷]-maximal-membership
      
          l {• x}   = Logic.[↔]-to-[←] decider-true
          l {⊤}     = Logic.[↔]-to-[←] [⊤]-maximal-membership
          l {¬ φ}   = Logic.[↔]-to-[←] [¬]-maximal-membership ∘ Logic.contrapositiveᵣ r
          l {φ ∧ ψ} = Logic.[↔]-to-[←] [∧]-maximal-membership ∘ Tuple.map l l
          l {φ ∨ ψ} = Logic.[↔]-to-[←] [∨]-maximal-membership ∘ Either.map l l
          l {φ ⟶ ψ} = Logic.[↔]-to-[←] [⟶]-maximal-membership ∘ Either.map (Logic.contrapositiveᵣ r) l
          l {φ ⟷ ψ} = Logic.[↔]-to-[←] [⟷]-maximal-membership ∘ Either.map (Tuple.map l l) (Tuple.map (Logic.contrapositiveᵣ r) (Logic.contrapositiveᵣ r))

        satisfiable : Satisfiable(Γ)
        satisfiable = Logic.[∃]-map-proof (\eq {φ} → Logic.[↔]-to-[→] (eq{φ})) equal-model-existence

    module ConsistentSubsetMaximality(p : ConsistentSubsetMaximality) where
      consistentElementMaximality : ConsistentElementMaximality
      consistentElementMaximality con = p con Left (Right [≡]-intro)

    module CompleteDerivability(p : CompleteDerivability) where
      module Consistent(consistent : Consistent(Γ)) where
        [⊢]-to-[∈]' : (Γ ⊢ φ) → (φ ∈ Γ)
        [⊢]-to-[∈]' {φ = φ} = Logic.[→]-disjunctive-formₗ {!!}

        consistentSubsetMaximality : ConsistentSubsetMaximality
        consistentSubsetMaximality {Δ} conΔ ΓΔ {φ} φΔ = {!Logic.[¬→]-disjunctive-formₗ (Either.map (weaken ΓΔ) (weaken ΓΔ) (p{φ}))!}
        {-with p{φ} | Logic.excluded-middle((¬ φ) ∈ Δ)
        ... | Left  q | Left  r = {!!}
        ... | Left  q | Right r with () ← Logic.contrapositiveᵣ(weaken ΓΔ) {!!} {!!}
        ... | Right q | _       with () ← conΔ([⊥]-intro (direct φΔ) (weaken ΓΔ q))-}
        -- conΔ([⊥]-intro (direct φΔ) (direct(ΓΔ ¬φΓ)))
        -- Logic.[∨]-not-right (p{φ}) (¬φΓ ↦ ?)

        consistentElementMaximality : ConsistentElementMaximality
        consistentElementMaximality {φ} conΓφ with p{φ} | Logic.excluded-middle((¬ φ) ∈ Γ)
        ... | Left  q | Left  r with () ← consistent([⊥]-intro q (direct r))
        ... | Left  q | Right r = Logic.[¬¬]-elim (¬Γφ ↦ {![⊢]-consistent-noncontradicting-membership consistent !})
        ... | Right q | _       with () ← conΓφ([¬]-intro-converse q)
        -- ConsistentSubsetMaximality.consistentElementMaximality {!!}
        -- [⊢]-derivability-consistencyᵣ consistent q
        -- [¬]-intro(Logic.[↔]-to-[→] [⊢]-derivability-inconsistency q)
        -- Logic.contrapositiveᵣ direct conΓφ
        -- (¬φΓ ↦ Logic.contrapositiveᵣ direct (conΓφ ∘ [¬]-intro-converse) {!r ∘ direct!})
        -- [⊢]-consistent-noncontradicting-membership consistent
        -- (r ∘ direct)

        completeMembership : CompleteMembership
        completeMembership = Either.map [⊢]-to-[∈] [⊢]-to-[∈] p where
          [⊢]-to-[∈] = (ConsistentElementMaximality.Consistent.[⊢]-to-[∈] consistentElementMaximality consistent)

  record MaximallyConsistent (Γ : Formulas(P){ℓ}) : Stmt{Lvl.𝐒(Lvl.of(P) Lvl.⊔ ℓ)} where
    field
      consistent : Consistent(Γ)
      maximal    : ConsistentlyComplete(Γ)

    subset-maximal  : ConsistentSubsetMaximality(Γ)
    element-maximal : ConsistentElementMaximality(Γ)

    element-maximal with maximal
    ... | subset-intro          p = ConsistentSubsetMaximality.consistentElementMaximality Γ p
    ... | element-intro         p = p
    ... | complete-deriv-intro  p = ConsistentSubsetMaximality.consistentElementMaximality Γ subset-maximal where
    ... | complete-member-intro p = ConsistentSubsetMaximality.consistentElementMaximality Γ (CompleteMembership.consistentSubsetMaximality Γ p)

    open ConsistentElementMaximality Γ element-maximal using
      ( element-maximal-contra
      ; [⊢]-derivability-consistencyₗ
      ) public

    open ConsistentElementMaximality.Consistent Γ element-maximal consistent using
      ( [⊢]-to-[∈]
      ; equal-model-existence
      ) public

    subset-maximal with maximal
    ... | subset-intro          p = p
    ... | element-intro         p = ConsistentElementMaximality.consistentSubsetMaximality Γ p
    ... | complete-deriv-intro  p = CompleteMembership.consistentSubsetMaximality Γ (Either.map [⊢]-to-[∈] [⊢]-to-[∈] p)
    ... | complete-member-intro p = CompleteMembership.consistentSubsetMaximality Γ p

    {-r : (term-model(max Γ con) ⊧ φ) → (φ ∈ max Γ con)
    r {• x}   modelsφ Γφ-incons = Logic.[↔]-to-[←] Logic.decide-is-true modelsφ Γφ-incons
    r {⊤}     modelsφ Γφ-incons = con([⊢]-compose-inconsistency [⊤]-intro Γφ-incons)-}

  open MaximallyConsistent ⦃ … ⦄ using
    ( [⊢]-derivability-consistencyₗ
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
        ... | Left  derp  | _ = [⊢]-compose-consistency derp (maxi-consistent con {n = n})
        ... | Right dernp | _ = [⊬]-negation-consistency(dernp ∘ [¬¬]-elim)
    -}

    maxi2 : Formulas(P){ℓ} → ℕ → Formulas(P){Lvl.of(P) Lvl.⊔ ℓ}
    maxi2 Γ 𝟎      = Lvl.Up{Lvl.of(P)} ∘ Γ
    maxi2 Γ (𝐒(n)) = let ψ = CountablyInfinite.index(Formula P) n
                     in  (maxi2 Γ n) ∪ singleton(if decide(0)(maxi2 Γ n ⊢ ψ) then ψ else (¬ ψ))

    maxi2-succ : let ψ = CountablyInfinite.index(Formula P) n in (((maxi2 Γ n) ∪ singleton(if decide(0)(maxi2 Γ n ⊢ ψ) then ψ else (¬ ψ))) ≡ₛ maxi2 Γ (𝐒(n)))
    -- maxi2-succ {n = n}{Γ = Γ} = Logic.[↔]-intro {!!} {!!}

    maxi2-zero : (Γ ≡ₛ maxi2 Γ 𝟎)
    maxi2-zero {Γ = Γ} = Logic.[↔]-symmetry (Sets.PredicateSet.LvlUp-set-equality {S = Γ})

    maxi2-superset : ∀{n} → (Γ ⊆ maxi2 Γ n)
    maxi2-superset {Γ = Γ} {𝟎}   = Logic.[↔]-to-[→] (maxi2-zero {Γ = Γ})
    maxi2-superset {Γ = Γ} {𝐒 n} = Left ∘ maxi2-superset {Γ = Γ} {n}

    instance
      maxi2-consistent : Consistent(Γ) → (∀{n} → Consistent(maxi2 Γ n))
      maxi2-consistent {Γ = Γ} con {n = 𝟎}   = [⊢]-subset-consistency (Logic.[↔]-to-[←] (maxi2-zero {Γ = Γ})) con
      maxi2-consistent {Γ = Γ} con {n = 𝐒 n} = [⊢]-subset-consistency (Logic.[↔]-to-[←] (maxi2-succ {Γ = Γ})) con-eq where
        p = CountablyInfinite.index(Formula P) n
        con-eq : Consistent((maxi2 Γ n) ∪ singleton(if decide(0)(maxi2 Γ n ⊢ p) then p else (¬ p)))
        con-eq with Logic.excluded-middle(maxi2 Γ n ⊢ p) | decide(0)(maxi2 Γ n ⊢ p)
        ... | Left  derp  | _ = [⊢]-compose-consistency derp (maxi2-consistent con {n = n})
        ... | Right dernp | _ = [⊬]-negation-consistency(dernp ∘ [¬¬]-elim)

    max : (Γ : Formulas(P){ℓ}) → Formulas(P){Lvl.of(P) Lvl.⊔ ℓ}
    max(Γ) φ = Logic.∃(n ↦ φ ∈ maxi2 Γ n)

    maxi2-subset-max : (maxi2 Γ n ⊆ max Γ)
    maxi2-subset-max {Γ = Γ} {n} p = Logic.[∃]-intro n ⦃ p ⦄

    open import Lang.Inspect
    max-maximal : (φ ∈ max Γ) Logic.∨ ((¬ φ) ∈ max Γ)
    max-maximal {φ = φ}{Γ = Γ}
      with n ← CountablyInfinite.indexing(Formula P) φ
      with Logic.excluded-middle(maxi2 Γ n ⊢ CountablyInfinite.index(Formula P) n) | inspect(maxi2 Γ) (𝐒 n)
    ... | Left  p | intro q with r ← congruence₁(_$ CountablyInfinite.index(Formula P) n) q = Left  (Logic.[∃]-intro (𝐒(n)) ⦃ Right {!!} ⦄)
    ... | Right p | intro q = Right (Logic.[∃]-intro (𝐒(n)) ⦃ Right {!q!} ⦄)

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
          β = CountablyInfinite.index(Formula P) b
        {-with Logic.excluded-middle(maxi2 Γ a ⊢ Logic.[∃]-witness Formula-is-countably-infinite a) | p
        ... | Left x | [≡]-intro = {!!}
        ... | Right x | q = test4 {a} {𝐒 b} {!!} {!!}-}

        -- TODO: Because test3 and test4
        test5 : Logic.∃(n ↦ (max Γ) ⊆ (maxi2 Γ n))

      -- with [∃]-intro n ⦃ pn ⦄ ← max Γ = {!!}
      -- [⊢]-subset-consistency (\{φ} → {!maxi2-consistent con {n = 𝟎}!}) {!con!}

    instance
      max-maximally-consistent : Consistent(Γ) → MaximallyConsistent(max Γ)
      MaximallyConsistent.consistent (max-maximally-consistent         con) = max-consistent con
      MaximallyConsistent.maximal    (max-maximally-consistent {Γ = Γ} con) = {!!}
      -- {φ} conm with n ← CountablyInfinite.indexing(Formula P) φ = {!!}

    max-superset : Γ ⊆ max Γ
    max-superset {Γ = Γ} Γφ = Logic.[∃]-intro 𝟎 ⦃ maxi2-superset {Γ = Γ}{n = 𝟎} Γφ ⦄

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
  test {con = con} p = [⊢]-compose-consistency ([¬]-intro(Logic.[¬¬]-elim p)) con

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
-}

module _ where
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

    consistency-of-∅ : Consistent{P = P}{ℓ = ℓ}(∅)
    consistency-of-∅ = satisfiable-consistent [∅]-satisfiable

  module _ where
    open import Data.Boolean.Stmt.Logic
    open import Lang.Inspect

    modelSet : Model(P) → Formulas(P)
    modelSet(𝔐) = 𝔐 ⊧_

    module _ {𝔐 : Model(P)} where
      modelSet-satisfiable : Satisfiable(modelSet(𝔐))
      modelSet-satisfiable = Logic.[∃]-intro 𝔐 ⦃ id ⦄

      modelSet-maximally-consistent : MaximallyConsistent(modelSet(𝔐))
      MaximallyConsistent.consistent modelSet-maximally-consistent = satisfiable-consistent modelSet-satisfiable
      MaximallyConsistent.maximal    modelSet-maximally-consistent = element-intro p where
        p : ConsistentElementMaximality(modelSet(𝔐))
        p {φ} cons with TruthTable.eval 𝔐 φ | inspect (TruthTable.eval 𝔐) φ
        ... | 𝑇 | intro eval-𝑇 = TruthTable.eval-to-models {φ = φ} (Logic.[↔]-to-[←] IsTrue.is-𝑇 eval-𝑇)
        ... | 𝐹 | intro eval-𝐹 = Logic.[⊥]-elim (cons ([⊥]-intro (direct (Right [≡]-intro)) (weaken Left (direct (TruthTable.eval-to-models {φ = ¬ φ} (Logic.[↔]-to-[←] IsTrue.is-𝑇 (congruence₁(BoolOp.¬) eval-𝐹)))))))

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
    term-model(Γ) p = decide(0)((• p) ∈ Γ)

  module _ ⦃ countable-P : CountablyInfinite(P) ⦄ where
    private variable Γ Γ₁ Γ₂ : Formulas(P){ℓₚ}

    term-model-of-max-proof : (con : Consistent(Γ)) → (max Γ ≡ₛ (term-model(max Γ) ⊧_))
    term-model-of-max-proof {Γ = Γ} con = Logic.[∃]-proof(MaximallyConsistent.equal-model-existence (max-maximally-consistent con))

    consistent-satisfiable : Consistent(Γ) → Satisfiable(Γ)
    Logic.∃.witness (consistent-satisfiable {Γ = Γ} con)     = term-model(max Γ)
    Logic.∃.proof   (consistent-satisfiable {Γ = Γ} con) {γ} = (Logic.[↔]-to-[→] (term-model-of-max-proof {Γ = Γ} con {γ})) ∘ max-superset

    completeness : (Γ ⊨ φ) → (Γ ⊢ φ)
    completeness {Γ = Γ}{φ = φ} =
      (Logic.[↔]-to-[←] [⊢]-derivability-inconsistency)
      ∘ (Logic.[↔]-to-[←] Logic.contrapositive-variant2 consistent-satisfiable)
      ∘ (Logic.[↔]-to-[→] [⊨]-entailment-unsatisfiability)
