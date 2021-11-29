module Structure.Type.Identity where

import      Lvl
open import Functional.Instance
open import Logic.Propositional
open import Logic
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type
open import Type.Properties.MereProposition
open import Type.Size

module _ {ℓ ℓₑ ℓₚ} {T : Type{ℓ}} (_≡_ : T → T → Stmt{ℓₑ}) where
  -- When a binary relation is the smallest reflexive relation (in the sense of cardinality of the relation set).
  -- This is one of many characterizations of equality.
  MinimalReflexiveRelation : Stmt
  MinimalReflexiveRelation = ∀{_▫_ : T → T → Stmt{ℓₚ}} → ⦃ refl : Reflexivity(_▫_) ⦄ → ((_≡_) ⊆₂ (_▫_))

  -- When a binary relation is able to substitute every unary relation and is satisfied when every unary relation .
  -- This is one of many characterizations of equality.
  GlobalSubstitution : Stmt
  GlobalSubstitution = ∀{x y : T} → ((x ≡ y) ↔ (∀{P : T → Type{ℓₚ}} → P(x) → P(y)))

module _ {ℓ ℓₑ ℓₘₑ} (T : Type{ℓ}) ⦃ equiv-T : Equiv{ℓₑ}(T) ⦄ ⦃ equiv-eq : ∀{x y : T} → Equiv{ℓₘₑ}(x ≡ y) ⦄ where
  -- A proof of identity is unique (there is only one inhabitant of the identity type).
  -- This is interpreted as saying that all proofs of an identity are equal to each other.
  -- Also called: Uniqueness of identity proofs (UIP).
  -- There is an axiom called "axiom UIP" which is a construction of the following type:
  -- • ∀{T} → UniqueIdentityProofs(T)
  UniqueIdentityProofs : Stmt
  UniqueIdentityProofs = ∀{x y : T} → MereProposition(x ≡ y)

module Names where
  module _ {ℓ ℓₑ ℓₚ} {T : Type{ℓ}} (Id : T → T → Stmt{ℓₑ}) ⦃ refl : Reflexivity(Id) ⦄ where
    -- Elimination rule for identity types.
    -- Also called J.
    -- Explanation:
    --   P{x}{y} (eq-proof) is an arbitrary predicate with possible mentions of an identity proof.
       --   A value of type (∀{x : T} → P(reflexivity(_≡_) {x})) means:
    --     reflexivity(_≡_) satisfies P for every pair of equal objects.
    --   The conclusion of the type (∀{x y : T} → (eq : (x ≡ y)) → P{x}{y}(eq)) means:
    --     Every identity proof satisfies P for every pair there is.
    --   In other words, to prove a proposition that depends on an identity proof, one only need to prove it for reflexivity.
    -- When this is joined by reflexivity, they become another characterization of equality.
    -- More information:
    -- • https://homotopytypetheory.org/2011/04/10/just-kidding-understanding-identity-elimination-in-homotopy-type-theory/
    -- • https://stackoverflow.com/questions/22580842/non-trivial-negation-in-agda
    IdentityEliminator : Stmt
    IdentityEliminator = (P : ∀{x y : T} → (Id x y) → Stmt{ℓₚ}) → (∀{x : T} → P(reflexivity(Id) {x})) → (∀{x y : T} → (eq : (Id x y)) → P(eq))

    -- Usage of the trivial equality reflexivity proof can be substituted by any proof of the same type.
    -- There is an axiom called "axiom K" which is a construction of the following type:
    -- • ∀{T} → IntroProofSubstitution(T)
    IntroProofSubstitution : Stmt
    IntroProofSubstitution = ∀{x : T}{P : (Id x x) → Type{ℓₚ}} → P(reflexivity(Id)) → (∀{eq : (Id x x)} → P(eq))

module _ {ℓ ℓₑ ℓₚ} {T : Type{ℓ}} (Id : T → T → Stmt{ℓₑ}) ⦃ refl : Reflexivity(Id) ⦄ where
  record IdentityEliminator : Stmt{ℓ Lvl.⊔ ℓₑ Lvl.⊔ Lvl.𝐒(ℓₚ)} where
    constructor intro
    field elim : Names.IdentityEliminator{ℓₚ = ℓₚ}(Id)
  idElim = inferArg IdentityEliminator.elim

module _
  {ℓ ℓₘ ℓₑ ℓₘₑ}
  {T : Type{ℓ}}
  (Id : T → T → Type{ℓₑ}) ⦃ refl-T :  Reflexivity(Id) ⦄  ⦃ identElim-T : IdentityEliminator(Id) ⦄
  (_≡_ : ∀{T : Type{ℓₘ}} → T → T → Type{ℓₘₑ})
  where

  open Reflexivity (refl-T) using () renaming (proof to refl)

  -- Reflexivity is an identity element for the identity elimination operation.
  record IdentityEliminationOfIntro : Stmt{ℓ Lvl.⊔ Lvl.𝐒 ℓₘ Lvl.⊔ ℓₑ Lvl.⊔ ℓₘₑ} where
    constructor intro
    field proof : (P : ∀{x y : T} → (Id x y) → Stmt{ℓₘ}) → (p : ∀{x} → P{x}{x}(refl)) → (∀{x : T} → (idElim(Id)(P) p refl ≡ p{x}))
  idElimOfIntro = inferArg IdentityEliminationOfIntro.proof

module _ {ℓₑ : Lvl.Level → Lvl.Level} (Id : ∀{ℓ}{T : Type{ℓ}} → T → T → Stmt{ℓₑ(ℓ)}) where
  record IdentityType : Stmtω where
    constructor intro
    field
      ⦃ identity-intro ⦄ : ∀{ℓₒ}{T : Type{ℓₒ}} → Reflexivity(Id{T = T})
      ⦃ identity-elim ⦄  : ∀{ℓₒ ℓₚ}{T : Type{ℓₒ}} → IdentityEliminator{ℓₚ = ℓₚ}(Id{T = T})
      ⦃ refl-elim-inverses ⦄ : ∀{ℓ ℓₘ}{T : Type{ℓ}} → IdentityEliminationOfIntro{ℓₘ = ℓₘ}(Id{T = T})(Id)
