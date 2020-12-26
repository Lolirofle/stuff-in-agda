module Structure.Type.Identity where

import      Lvl
open import Lang.Instance
open import Logic.Propositional
open import Logic
open import Structure.Relator.Properties renaming (reflexivity to reflexivity')
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
  -- A proof of equality is unique (when both equivalences are the same: using equality itself to determine uniqueness).
  -- This is interpreted as saying that all proofs of an equality are equal to each other.
  -- Also called: Uniqueness of identity proofs (UIP).
  -- There is an axiom called "axiom UIP" which is a construction of the following type:
  -- • ∀{T} → UniqueIdentityProofs(T)
  UniqueIdentityProofs : Stmt
  UniqueIdentityProofs = ∀{x y : T} → MereProposition(x ≡ y)

module Names where
  module _ {ℓ ℓₑ ℓₚ} {T : Type{ℓ}} (_≡_ : T → T → Stmt{ℓₑ}) ⦃ refl : Reflexivity(_≡_) ⦄ where
    -- Elimination rule for identity types.
    -- Also called J.
    -- Explanation:
    --   P{x}{y} (eq-proof) is an arbitrary predicate with possible mentions of an equality proof.
       --   A value of type (∀{x : T} → P{x}{x}([≡]-intro)) means:
    --     [≡]-intro satisfies P for every pair with equal elements.
    --   The conclusion of type (∀{x y : T} → (eq : (x ≡ y)) → P{x}{y}(eq)) means:
    --     Every equality proof satisfies P for every pair there is.
    -- TODO: https://homotopytypetheory.org/2011/04/10/just-kidding-understanding-identity-elimination-in-homotopy-type-theory/
    -- TODO: Usage: https://stackoverflow.com/questions/22580842/non-trivial-negation-in-agda
    IdentityEliminator : Stmt
    IdentityEliminator = (P : ∀{x y : T} → (x ≡ y) → Stmt{ℓₚ}) → (∀{x : T} → P{x}{x}(reflexivity'(_≡_))) → (∀{x y : T} → (eq : (x ≡ y)) → P{x}{y}(eq))

    -- Usage of the trivial equality reflexivity proof can be substituted by any proof of the same type.
    -- There is an axiom called "axiom K" which is a construction of the following type:
    -- • ∀{T} → IntroProofSubstitution(T)
    IntroProofSubstitution : Stmt
    IntroProofSubstitution = ∀{x : T}{P : (x ≡ x) → Type{ℓₚ}} → P(reflexivity'(_≡_)) → (∀{eq : (x ≡ x)} → P(eq))

  {-module _ {ℓₑ : Lvl.Level → Lvl.Level}{ℓₒ ℓₚ} (_≡_ : ∀{ℓ}{T : Type{ℓ}} → T → T → Stmt{ℓₑ(ℓ)}) ⦃ refl : ∀{T : Type{ℓₒ}} → Reflexivity(_≡_ {T = T}) ⦄ where
    IdentityEliminationOfIntro : (∀{T : Type{ℓₒ}} → IdentityEliminator(_≡_ {T = T})) → Stmt
    IdentityEliminationOfIntro(idElim) = ∀{T : Type{ℓₒ}} → (P : ∀{x y : T} → (x ≡ y) → Stmt{ℓₚ}) → (p : ∀{x} → P{x}{x}(reflexivity'(_≡_))) → (∀{x : T} → (idElim(P) p (reflexivity'(_≡_)) ≡ p{x}))
  -}

module _ {ℓ ℓₑ ℓₚ} {T : Type{ℓ}} (_≡_ : T → T → Stmt{ℓₑ}) ⦃ refl : Reflexivity(_≡_) ⦄ where
  record IdentityEliminator : Stmt{ℓ Lvl.⊔ ℓₑ Lvl.⊔ Lvl.𝐒(ℓₚ)} where
    constructor intro
    field proof : Names.IdentityEliminator{ℓₚ = ℓₚ}(_≡_)
  idElim = inst-fn IdentityEliminator.proof

module _
  {ℓ ℓₘ ℓₑ ℓₘₑ}
  {T : Type{ℓ}}
  {_≡_ : T → T → Type{ℓₑ}} ⦃ refle-T :  Reflexivity(_≡_) ⦄  ⦃ identElim-T : IdentityEliminator(_≡_) ⦄
  {_≡ₘ_ : ∀{T : Type{ℓₘ}} → T → T → Type{ℓₘₑ}}
  where

  open Reflexivity (refle-T) using () renaming (proof to refl)

  record IdentityEliminationOfIntro : Stmt{ℓ Lvl.⊔ Lvl.𝐒 ℓₘ Lvl.⊔ ℓₑ Lvl.⊔ ℓₘₑ} where
    constructor intro
    field proof : (P : ∀{x y : T} → (x ≡ y) → Stmt{ℓₘ}) → (p : ∀{x} → P{x}{x}(refl)) → (∀{x : T} → (idElim(_≡_)(P) p refl ≡ₘ p{x}))
  idElimOfIntro = inst-fn IdentityEliminationOfIntro.proof

{-
module _ {ℓₑ : Lvl.Level → Lvl.Level} (_≡_ : ∀{ℓ}{T : Type{ℓ}} → T → T → Stmt{ℓₑ(ℓ)}) where
  record IdentityType : Stmtω where
    constructor intro
    field
      ⦃ identity-intro ⦄ : ∀{ℓₒ}{T : Type{ℓₒ}} → Reflexivity(_≡_ {T = T})
      ⦃ identity-elim ⦄  : ∀{ℓₒ ℓₚ}{T : Type{ℓₒ}} → IdentityEliminator{ℓₚ = ℓₚ}(_≡_ {T = T})
      elim-of-intro : ∀{ℓₒ ℓₚ} → Names.IdentityEliminationOfIntro{ℓₑ = ℓₑ}{ℓₒ = ℓₒ}{ℓₚ = ℓₚ}(_≡_)(idElim(_≡_))
-}
