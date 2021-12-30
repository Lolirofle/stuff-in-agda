{-# OPTIONS --cubical #-}

open import Formalization.PredicateLogic.Signature

module Formalization.PredicateLogic.Constructive.SequentCalculus (𝔏 : Signature) where
open Signature(𝔏)

open import Data.Option
open import Data.List
open import Data.List.Functions using (map) renaming (singleton to · ; _++_ to _∪_)
open import Data.List.Relation.Permutation
import      Data.ListSized as S
open import Formalization.PredicateLogic.Syntax(𝔏)
open import Formalization.PredicateLogic.Syntax.Substitution(𝔏)
open import Functional as Fn using ()
import      Lvl
open import Numeral.Natural
open import Type

private variable ℓ : Lvl.Level
private variable args n vars vars₁ vars₂ : ℕ
private variable Γ Γ₁ Γ₂ Γ₃ : List(Formula(vars))
private variable Δ Δ₁ Δ₂ Δ₃ : Option(Formula(vars))
private variable φ φ₁ φ₂ ψ A B C : Formula(vars)
private variable p : Prop(n)
private variable f : Prop(args)
private variable x : S.List(Term(vars))(args)

_∪·_ : ∀{T : Type{ℓ}} → List(T) → T → List(T)
_∪·_ = Fn.swap(_⊰_)
infixl 1000 _∪·_

module Variant1 where
  data _⇒_ : List(Formula(vars)) → Option(Formula(vars)) → Type{Lvl.𝐒(ℓₚ Lvl.⊔ ℓₒ)} where
    axiom : ((· φ) ⇒ Some(φ))

    weakenₗ : (Γ ⇒ Δ) → ((Γ ∪· A) ⇒ Δ)
    permuteₗ : (Γ₁ permutes Γ₂) → (Γ₁ ⇒ Δ) → (Γ₂ ⇒ Δ)
    contractₗ : ((Γ ∪· A ∪· A) ⇒ Δ) → ((Γ ∪· A) ⇒ Δ)
    ⊥ₗ : (Γ ∪· ⊥) ⇒ None
    ∧ₗₗ : ((Γ ∪· A) ⇒ Δ) → ((Γ ∪· (A ∧ B)) ⇒ Δ)
    ∧ₗᵣ : ((Γ ∪· B) ⇒ Δ) → ((Γ ∪· (A ∧ B)) ⇒ Δ)
    ∨ₗ : ((Γ ∪· A) ⇒ Δ) → ((Γ ∪· B) ⇒ Δ) → ((Γ ∪· (A ∨ B)) ⇒ Δ)
    ⟶ₗ : (Γ ⇒ Some(A)) → ((Γ ∪· B) ⇒ Δ) → ((Γ ∪· (A ⟶ B)) ⇒ Δ)
    Ɐₗ : ∀{t} → ((Γ ∪· (substitute0 t A)) ⇒ Δ) → ((Γ ∪· (Ɐ A)) ⇒ Δ)
    ∃ₗ : ∀{v}{n} → ((Γ ∪· (substituteN n (var v) A)) ⇒ Δ) → ((Γ ∪· (∃ A)) ⇒ Δ)

    weakenᵣ : (Γ ⇒ None) → (Γ ⇒ Some(A))
    ⊤ᵣ : ∅ ⇒ Some(⊤ {vars})
    ∧ᵣ : (Γ ⇒ Some(A)) → (Γ ⇒ Some(B)) → (Γ ⇒ Some(A ∧ B))
    ∨ᵣₗ : (Γ ⇒ Some(A)) → (Γ ⇒ Some(A ∨ B))
    ∨ᵣᵣ : (Γ ⇒ Some(B)) → (Γ ⇒ Some(A ∨ B))
    ⟶ᵣ : ((Γ ∪· A) ⇒ Some(B)) → (Γ ⇒ Some(A ⟶ B))
    Ɐᵣ : ∀{v}{n} → (Γ ⇒ Some((substituteN n (var v) A))) → (Γ ⇒ Some(Ɐ A))
    ∃ᵣ : ∀{t} → (Γ ⇒ Some((substitute0 t A))) → (Γ ⇒ Some(∃ A))

  import Logic.Propositional as Meta

  no-empty-refl : Meta.¬(∅ ⇒ None{T = Formula vars})
  no-empty-refl (permuteₗ perm p) rewrite Proofs.permutes-on-empty perm = no-empty-refl p

  {-
  no-callCC : Meta.¬(∅ ⇒ Some(((A ⟶ B) ⟶ A) ⟶ A))
  no-callCC (permuteₗ perm p) rewrite permutes-on-empty perm = no-callCC p
  no-callCC (weakenᵣ (permuteₗ perm p)) rewrite permutes-on-empty perm = no-empty-refl p
  no-callCC (⟶ᵣ p) = no-callCC {!!}
  {-no-callCC (⟶ᵣ (weakenₗ p)) = {!!}
  no-callCC (⟶ᵣ (permuteₗ x p)) = {!!}
  no-callCC (⟶ᵣ (contractₗ p)) = {!!}
  no-callCC (⟶ᵣ (⟶ₗ p p₁)) = {!!}
  no-callCC (⟶ᵣ (weakenᵣ p)) = {!!}
  no-callCC (⟶ᵣ (∧ᵣ p p₁)) = {!!}
  no-callCC (⟶ᵣ (∨ᵣₗ p)) = {!!}
  no-callCC (⟶ᵣ (∨ᵣᵣ p)) = {!!}
  no-callCC (⟶ᵣ (⟶ᵣ p)) = {!!}
  no-callCC (⟶ᵣ (Ɐᵣ p)) = {!!}
  no-callCC (⟶ᵣ (∃ᵣ p)) = {!!}
  -}
  -}

module Variant3 where
  -- Note: Because this formalization is non-standard, a problem arises for Formula(𝟎): It it missing some of the quantification rules because it has no variables.
  data _⇒_ : List(Formula(vars)) → Formula(vars) → Type{Lvl.𝐒(ℓₚ Lvl.⊔ ℓₒ)} where
    axiom : ((Γ ∪· (f $ x)) ⇒ (f $ x))

    permuteₗ : (Γ₁ permutes Γ₂) → (Γ₁ ⇒ C) → (Γ₂ ⇒ C)
    ⊥ₗ : (Γ ∪· ⊥) ⇒ A
    ∧ₗ : ((Γ ∪· A ∪· B) ⇒ C) → ((Γ ∪· (A ∧ B)) ⇒ C)
    ∨ₗ : ((Γ ∪· A) ⇒ C) → ((Γ ∪· B) ⇒ C) → ((Γ ∪· (A ∨ B)) ⇒ C)
    ⟶ₗ : ((Γ ∪· (A ⟶ B)) ⇒ A) → ((Γ ∪· B) ⇒ C) → ((Γ ∪· (A ⟶ B)) ⇒ C)
    Ɐₗ : ∀{t} → ((Γ ∪· (substitute0 t A) ∪· (Ɐ A)) ⇒ C) → ((Γ ∪· (Ɐ A)) ⇒ C)
    ∃ₗ : ∀{n}{v} → ((Γ ∪· (substituteN n (var v) A)) ⇒ C) → ((Γ ∪· (∃ A)) ⇒ C)

    ⊤ᵣ : Γ ⇒ (⊤ {vars})
    ∧ᵣ : (Γ ⇒ A) → (Γ ⇒ B) → (Γ ⇒ (A ∧ B))
    ∨ᵣₗ : (Γ ⇒ A) → (Γ ⇒ (A ∨ B))
    ∨ᵣᵣ : (Γ ⇒ B) → (Γ ⇒ (A ∨ B))
    ⟶ᵣ : ((Γ ∪· A) ⇒ B) → (Γ ⇒ (A ⟶ B))
    Ɐᵣ : ∀{n}{v} → (Γ ⇒ (substituteN n (var v) A)) → (Γ ⇒ (Ɐ A))
    ∃ᵣ : ∀{t} → (Γ ⇒ (substitute0 t A)) → (Γ ⇒ (∃ A))

  import      Logic.Propositional as Meta
  open import Numeral.Finite
  open import Type.Properties.Inhabited

  weakenₗ : (Γ ⇒ ψ) → ((Γ ∪· φ) ⇒ ψ)
  weakenₗ axiom          = permuteₗ swap axiom
  weakenₗ (permuteₗ x p) = permuteₗ (prepend x) (weakenₗ p)
  weakenₗ ⊥ₗ             = permuteₗ swap ⊥ₗ
  weakenₗ (∧ₗ p)         = permuteₗ swap (∧ₗ(permuteₗ (trans swap (prepend swap)) (weakenₗ p)))
  weakenₗ (∨ₗ p q)       = permuteₗ swap (∨ₗ (permuteₗ swap (weakenₗ p)) (permuteₗ swap (weakenₗ q)))
  weakenₗ (⟶ₗ p q)       = permuteₗ swap (⟶ₗ (permuteₗ swap (weakenₗ p)) (permuteₗ swap (weakenₗ q)))
  weakenₗ (Ɐₗ p)         = permuteₗ swap (Ɐₗ (permuteₗ (trans swap (prepend swap)) (weakenₗ p)))
  weakenₗ (∃ₗ{n = n} p)  = permuteₗ swap (∃ₗ{n = n} (permuteₗ swap (weakenₗ p)))
  weakenₗ ⊤ᵣ             = ⊤ᵣ
  weakenₗ (∧ᵣ  p q)      = ∧ᵣ (weakenₗ p) (weakenₗ q)
  weakenₗ (∨ᵣₗ p)        = ∨ᵣₗ (weakenₗ p)
  weakenₗ (∨ᵣᵣ p)        = ∨ᵣᵣ (weakenₗ p)
  weakenₗ (⟶ᵣ  p)        = ⟶ᵣ (permuteₗ swap (weakenₗ p))
  weakenₗ (Ɐᵣ{n = n} p)  = Ɐᵣ{n = n} (weakenₗ p)
  weakenₗ (∃ᵣ  p)        = ∃ᵣ (weakenₗ p)

  weaken-union : (Γ₂ ⇒ φ) → ((Γ₁ ∪ Γ₂) ⇒ φ)
  weaken-union {Γ₁ = ∅}      p = p
  weaken-union {Γ₁ = φ ⊰ Γ₁} p = weakenₗ (weaken-union {Γ₁ = Γ₁} p)

  open import Formalization.PredicateLogic.Syntax.Tree(𝔏)
  open import Numeral.Natural.Relation.Order
  open import Numeral.Natural.Relation.Order.Proofs
  open import Relator.Equals
  open import Relator.Equals.Proofs
  open import Structure.Function
  open import Structure.Relator.Properties
  open import Syntax.Function

  direct₊ : ∀{φ : Formula(𝐒(vars))} → ((Γ ∪· φ) ⇒ φ)
  direct₊{Γ = Γ}{φ = φ} = induction-on-height(P) (\{vars}{φ} → proof{vars}{φ}) \() where
    P = \{vars} (φ : Formula(vars)) → (vars ≢ 𝟎) → ∀{Γ} → (Γ ∪· φ) ⇒ φ
    proof : ∀{φ : Formula(vars)} → (∀{vars}{ψ : Formula(vars)} → (height ψ < height φ) → P(ψ)) → P(φ)
    proof {𝟎}               _    nz with () ← nz [≡]-intro
    proof {𝐒 _} {φ = f $ x} prev _  = axiom
    proof {𝐒 _} {φ = ⊤}     prev _  = weakenₗ ⊤ᵣ
    proof {𝐒 _} {φ = ⊥}     prev _  = ⊥ₗ
    proof {𝐒 _} {φ = φ ∧ ψ} prev nz = ∧ᵣ (∧ₗ (permuteₗ swap (prev (∧-height-orderₗ{φ = φ}{ψ = ψ}) nz))) (∧ₗ (prev (∧-height-orderᵣ{ψ = ψ}{φ = φ}) nz))
    proof {𝐒 _} {φ = φ ∨ ψ} prev nz = ∨ₗ (∨ᵣₗ (prev (∨-height-orderₗ{φ = φ}{ψ = ψ}) nz)) (∨ᵣᵣ (prev (∨-height-orderᵣ{ψ = ψ}{φ = φ}) nz))
    proof {𝐒 _} {φ = φ ⟶ ψ} prev nz = ⟶ᵣ (permuteₗ swap (⟶ₗ (permuteₗ swap (prev (⟶-height-orderₗ{φ = φ}{ψ = ψ}) nz)) (prev (⟶-height-orderᵣ{ψ = ψ}{φ = φ}) nz)))
    proof {𝐒 v} {φ = Ɐ φ}   prev nz = Ɐᵣ{n = 𝟎}{v = 𝟎} (Ɐₗ{t = var 𝟎} (weakenₗ (prev (subtransitivityₗ(_≤_)(_≡_) (congruence₁(𝐒) (substitute-height{φ = φ})) (Ɐ-height-order{φ = φ})) nz)))
    proof {𝐒 v} {φ = ∃ φ}   prev nz = ∃ᵣ{t = var 𝟎} (∃ₗ{n = 𝟎}{v = 𝟎} (prev (subtransitivityₗ(_≤_)(_≡_) (congruence₁(𝐒) (substitute-height{φ = φ})) (Ɐ-height-order{φ = φ})) nz))

  no-empty-refl : Meta.¬(∅ ⇒ (⊥ {vars}))
  no-empty-refl (permuteₗ perm p) rewrite Proofs.permutes-on-empty perm = no-empty-refl p

  no-empty-axiomₗ : Meta.¬(·(p $ x) ⇒ ⊥)
  no-empty-axiomₗ (permuteₗ perm p) rewrite Proofs.permutes-on-singleton perm = no-empty-axiomₗ p

  no-empty-axiomᵣ : Meta.¬(∅ ⇒ (p $ x))
  no-empty-axiomᵣ (permuteₗ perm p) rewrite Proofs.permutes-on-empty perm = no-empty-axiomᵣ p

  no-negated-axiomᵣ : Meta.¬(∅ ⇒ (¬(p $ x)))
  no-negated-axiomᵣ (permuteₗ perm p) rewrite Proofs.permutes-on-empty perm = no-negated-axiomᵣ p
  no-negated-axiomᵣ (⟶ᵣ p) = no-empty-axiomₗ p

  -- 3.5.2
  substitute-proof : ∀{t : 𝕟(vars₁) → Term(vars₂)} → (Γ ⇒ φ) → ((map(substitute t) Γ) ⇒ (substitute t φ))
  substitute-proof p = {!!}

  module _ ⦃ pos-prop : ◊(Prop(0)) ⦄ where
    no-excludedMiddle : Meta.¬(∀{A : Formula(vars)} → (∅ ⇒ (A ∨ (¬ A))))
    no-excludedMiddle as = proof(as{inhabitant $ S.∅}) where
      proof : Meta.¬(∅ ⇒ ((p $ x) ∨ ¬(p $ x)))
      proof (permuteₗ perm q)            rewrite Proofs.permutes-on-empty perm = proof q
      proof (∨ᵣₗ (permuteₗ perm q))      rewrite Proofs.permutes-on-empty perm = no-empty-axiomᵣ q
      proof (∨ᵣᵣ (permuteₗ perm q))      rewrite Proofs.permutes-on-empty perm = no-negated-axiomᵣ q
      proof (∨ᵣᵣ (permuteₗ perm (⟶ᵣ q))) rewrite Proofs.permutes-on-empty perm = no-empty-axiomₗ q
      proof (∨ᵣᵣ (⟶ᵣ (permuteₗ perm q))) rewrite Proofs.permutes-on-singleton perm = no-empty-axiomₗ q

    no-doubleNegation : Meta.¬(∀{A : Formula(vars)} → (∅ ⇒ ((¬ ¬ A) ⟶ A)))
    no-doubleNegation as = proof(as{inhabitant $ S.∅}) where
      proof : Meta.¬(∅ ⇒ ((¬ ¬(p $ x)) ⟶ (p $ x)))
      proof (permuteₗ perm q) rewrite Proofs.permutes-on-empty perm = proof q
      proof (⟶ᵣ (permuteₗ perm q)) = {!!}
      proof (⟶ᵣ (⟶ₗ q (permuteₗ perm q₁))) = {!!}
      proof (⟶ᵣ (⟶ₗ (permuteₗ perm q) ⊥ₗ)) = {!!}
      proof (⟶ᵣ (⟶ₗ (⟶ₗ q q₁) ⊥ₗ)) = {!!}
      proof (⟶ᵣ (⟶ₗ (⟶ᵣ q) ⊥ₗ)) = {!!}

    test : ∀{T : Type{ℓ}} → (Γ₁ permutes Γ₂) → ((Γ₁ ⇒ φ) → T) → ((Γ₂ ⇒ φ) → T)
    test perm p1 p2 = p1 (permuteₗ (symmetry(_permutes_) perm) p2)
    {-# INLINE test #-}

    no-callCC : Meta.¬(∀{A B : Formula(vars)} → (∅ ⇒ ((A ⟶ B) ⟶ A) ⟶ A))
    no-callCC as = proof(as{inhabitant $ S.∅}{⊥}) where
      proof2 : Meta.¬((∅ ∪· ((p $ x ⟶ ⊥) ⟶ p $ x) ∪· p $ x) ⇒ ⊥)
      proof2 (permuteₗ x t) = {!t!}

      proof3 : Meta.¬((∅ ∪· p $ x ∪· ((p $ x ⟶ ⊥) ⟶ p $ x)) ⇒ ⊥)
      proof3 (permuteₗ perm p) = {!!}
      proof3 (⟶ₗ p q) = {!!}

      proof : Meta.¬(∅ ⇒ (((p $ x) ⟶ ⊥) ⟶ (p $ x)) ⟶ (p $ x))
      proof (permuteₗ perm q) rewrite Proofs.permutes-on-empty perm = proof q
      proof (⟶ᵣ (permuteₗ perm q)) rewrite Proofs.permutes-on-singleton perm = {!!}
      proof (⟶ᵣ (⟶ₗ (permuteₗ perm q) q₁)) = {!!}
      proof (⟶ᵣ (⟶ₗ (⟶ₗ q (permuteₗ x r)) s)) = {!!}
      proof (⟶ᵣ (⟶ₗ (⟶ₗ q (⟶ᵣ r)) s)) = no-empty-axiomₗ (contract-axiom-bottom r) where
        contract-axiom-bottom : ((·(p $ x) ∪· (p $ x)) ⇒ ⊥) → (·(p $ x) ⇒ ⊥)
        contract-axiom-bottom (permuteₗ x p) = {!!}
      proof (⟶ᵣ (⟶ₗ (⟶ᵣ (permuteₗ perm q)) r)) = proof2 (permuteₗ perm q)

      -- proof (⟶ᵣ (⟶ₗ (⟶ᵣ (permuteₗ perm q)) r)) = test (trans swap (symmetry(_permutes_) perm)) (proof ↦ {!⟶ᵣ proof!}) q
      {-proof (⟶ᵣ (⟶ₗ (⟶ᵣ (permuteₗ perm q)) r)) = test (symmetry(_permutes_) perm) proof2 q where
        proof2 : Meta.¬((∅ ∪· ((p $ x ⟶ ⊥) ⟶ p $ x) ∪· p $ x) ⇒ ⊥)
        proof2 (permuteₗ perm p) = test (symmetry(_permutes_) perm) proof2 p-}
        
      {-proof (⟶ᵣ (⟶ₗ (⟶ᵣ (permuteₗ (prepend perm) q)) r)) rewrite permutes-on-singleton perm = {!!}
      proof (⟶ᵣ (⟶ₗ (⟶ᵣ (permuteₗ swap (permuteₗ perm q))) r)) = {!!}
      proof (⟶ᵣ (⟶ₗ (⟶ᵣ (permuteₗ swap (⟶ₗ q₁ (permuteₗ perm q₂)))) r)) = {!!}
      proof (⟶ᵣ (⟶ₗ (⟶ᵣ (permuteₗ (trans perm₁ perm₂) q)) r)) = {!!}-}

     --⟶ₗ : ((Γ ∪· (A ⟶ B)) ⇒ A) → ((Γ ∪· B) ⇒ A) → ((Γ ∪· (A ⟶ B)) ⇒ A)
