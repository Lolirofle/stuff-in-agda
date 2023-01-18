{-# OPTIONS --cubical #-}

module Type.Cubical.Isomorphism.Equiv where

open import BidirectionalFunction
open import Function
open import Function.Domains
open import Logic.Predicate
import      Lvl
open import Structure.Relator
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Structure.Type.Identity
open import Type.Cubical
open import Type.Cubical.Isomorphism
open import Type.Cubical.Path.Equality
open import Type.Cubical.Path.Functions
open import Type.Dependent.Sigma
import      Type.Isomorphism.Equiv as Type
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₚ : Lvl.Level
private variable A B : Type{ℓ}

instance
  [≍][↔]-sub : (_≍_ {ℓ₁}{ℓ₂}) ⊆₂ (_↔_)
  [≍][↔]-sub = intro [∃]-witness

instance
  [≍][→]-sub : (_≍_ {ℓ₁}{ℓ₂}) ⊆₂ (_→ᶠ_)
  [≍][→]-sub = intro \eq → sub₂(_≍_)(_↔_) eq $ᵣ_

[≍]-reflexivity-raw  = \{ℓ}{T : Type{ℓ}} → Type.[≍]-reflexivity-raw {T = T} ⦃ Path-equiv ⦄
[≍]-symmetry-raw     = \{ℓ₁}{A : Type{ℓ₁}}{ℓ₂}{B : Type{ℓ₂}} → Type.[≍]-symmetry-raw {A = A}{B = B} ⦃ Path-equiv ⦄ ⦃ Path-equiv ⦄
[≍]-transitivity-raw = \{ℓ₁}{A : Type{ℓ₁}}{ℓ₂}{B : Type{ℓ₂}}{ℓ₃}{C : Type{ℓ₃}} → Type.[≍]-transitivity-raw {A = A}{B = B}{C = C} ⦃ Path-equiv ⦄ ⦃ Path-equiv ⦄ ⦃ Path-equiv ⦄ ⦃ Path-congruence₁ ⦄ ⦃ Path-congruence₁ ⦄

instance
  [≍]-reflexivity = \{ℓ} → Type.[≍]-reflexivity {ℓ} ⦃ Path-equiv ⦄

instance
  [≍]-symmetry = \{ℓ} → Type.[≍]-symmetry {ℓ} ⦃ Path-equiv ⦄

instance
  [≍]-transitivity = \{ℓ} → Type.[≍]-transitivity {ℓ} ⦃ Path-equiv ⦄ ⦃ Path-congruence₁ ⦄

instance
  [≍]-equivalence = \{ℓ} → Type.[≍]-equivalence {ℓ} ⦃ Path-equiv ⦄ ⦃ Path-congruence₁ ⦄

[≍][→]-sub-raw : Names.Sub₂(_≍_ {ℓ₁}{ℓ₂})(_→ᶠ_)
[≍][→]-sub-raw = sub₂(_≍_)(_→ᶠ_)
{-# BUILTIN EQUIVFUN [≍][→]-sub-raw #-}

postulate [≍][→]-sub-partial-extract : ∀(A : Type{ℓ₁})(B : Type{ℓ₂}) → (ab : A ≍ B) → (b : B) → (i : Interval) → (Interval.Partial i (Σ A (Fiber(sub₂(_≍_)(_→ᶠ_) ab) b))) → Σ A (Fiber(sub₂(_≍_)(_→ᶠ_) ab) b)
{-# BUILTIN EQUIVPROOF [≍][→]-sub-partial-extract #-}

open import Type.Cubical.Path
open import Type.Dependent.Sigma as Σ

open import Structure.Function
open import Structure.Function.Domain
import      Structure.Function.Names as Names
open import Structure.Operator
open import Type.Cubical.Path.Proofs
open import Type.Properties.MereProposition

{-
  [≍][→]-sub-injective : Injective(sub₂(_≍_)(_→ᶠ_) {A}{B})
  [≍][→]-sub-injective = intro \{iso₁}{iso₂} eq i → [∃]-intro {!eq i!} ⦃ {!!} ⦄
-}

-- TODO: Is this actually provable? Not sure when paths are mere props
-- TODO: Maybe not possible. See https://golem.ph.utexas.edu/category/2011/03/homotopy_type_theory_ii.html
instance
  postulate Inverses-prop : ∀{f : A → B}{f⁻¹ : A ← B} → MereProposition(Names.Inverses(f)(f⁻¹))
  {-MereProposition.uniqueness(Inverses-prop{A = A}{B = B}{f}{f⁻¹}) {p}{q} i {x} j =
    Interval.hComp (\k → \{
      (i = Interval.𝟎) → q {!Interval.max j k!} ;
      (i = Interval.𝟏) → p{{!!}} i ;
      (j = Interval.𝟎) → {!f(f⁻¹ ?)!} ; -- f(f⁻¹(x))
      (j = Interval.𝟏) → x
    })
    x
{-
i = Interval.𝟎 ⊢ p j
i = Interval.𝟏 ⊢ q j
j = Interval.𝟎 ⊢ (f Functional.∘ f⁻¹) x
j = Interval.𝟏 ⊢ x
-}
-}

instance
  -- TODO: If Inverses-prop is provable, use it to prove this
  postulate InversePair-prop : ∀{f : A ↔ B} → MereProposition(InversePair(f))
  {-InversePair-prop{A = A}{B = B}{f = f} = intro \{ {intro ⦃ left = intro pₗ ⦄ ⦃ right = intro pᵣ ⦄} {intro ⦃ left = intro qₗ ⦄ ⦃ right = intro qᵣ ⦄} →
    congruence₂(\l r → intro ⦃ left = l ⦄ ⦃ right = r ⦄)
      (congruence₁(intro) {!uniqueness(Names.Inverses{A = A}{B = B}(f $ᵣ_)(f $ₗ_)) {pₗ}{qₗ}!})
      (congruence₁(intro) (uniqueness(Names.Inverses(f $ₗ_)(f $ᵣ_)) {pᵣ}{qᵣ}))
    }-}

instance
  -- TODO: Prove this
  -- This is used in the proof of path univalence.
  [≍]-identityElim : IdentityEliminator(_≍_ {ℓ}) {ℓₚ}
  IdentityEliminator.elim [≍]-identityElim P p {X}{Y} eq = substitute₁ᵣ(\(intro X eq) → P{X}{Y} eq) proof p where
    postulate proof : Path{P = Σ Type (_≍ Y)} (Σ.intro Y (reflexivity(_≍_))) (Σ.intro X eq)
    -- proof i = {!!}

instance
  -- sub₂(_≍_)(_↔_) is injective because (_≍_) only consist of two fields: The field that sub₂(_≍_)(_↔_) returns and an InversePair of it, and InversePair(_) is a mere proposition, so the first field determines the equality.
  [≍][↔]-sub-injective : Injective(sub₂(_≍_)(_↔_) {A}{B})
  [≍][↔]-sub-injective = intro \eq → mapP₂(\x p → [∃]-intro x ⦃ p ⦄) eq (interval-predicate₁-path ⦃ \{ab} → InversePair-prop {f = ab} ⦄ eq)
