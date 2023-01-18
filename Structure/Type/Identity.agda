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
  -- When joined with reflexivity, they becomes one of many characterizations of equality.
  MinimalReflexiveRelation : Stmt
  MinimalReflexiveRelation = ∀{_▫_ : T → T → Stmt{ℓₚ}} → ⦃ refl : Reflexivity(_▫_) ⦄ → ((_≡_) ⊆₂ (_▫_))

  -- When a binary relation have the substitution property for every unary relation and is determined by predicate implication for any predicate.
  -- This is one of many characterizations of equality.
  GlobalSubstitution : Stmt
  GlobalSubstitution = ∀{x y : T} → ((x ≡ y) ↔ ((P : T → Type{ℓₚ}) → P(x) → P(y)))

module _ {ℓ ℓₑ ℓₘₑ} (T : Type{ℓ}) ⦃ equiv-T : Equiv{ℓₑ}(T) ⦄ ⦃ equiv-eq : ∀{x y : T} → Equiv{ℓₘₑ}(x ≡ y) ⦄ where
  -- A proof of identity is unique (there is only one inhabitant of the identity type).
  -- This is interpreted as saying that all proofs of an identity are equal to each other.
  -- Also called: Uniqueness of identity proofs (UIP), h-prop property of the identity type, h-set property of the underlying type.
  -- There is an axiom called "axiom UIP" which is a construction of the following type:
  -- • ∀{T} → UniqueIdentityProofs(T)
  UniqueIdentityProofs : Stmt
  UniqueIdentityProofs = ∀{x y : T} → MereProposition(x ≡ y)

module Names where
  module _ {ℓ ℓₑ} {T : Type{ℓ}} (Id : T → T → Stmt{ℓₑ}) ⦃ refl : Reflexivity(Id) ⦄ where
    -- Elimination rule for identity types.
    -- Also called: J.
    -- Explanation:
    --   P{x}{y} (eq-proof) is an arbitrary predicate with possible mentions of an identity proof.
       --   A value of type (∀{x : T} → P(reflexivity(_≡_) {x})) means:
    --     reflexivity(_≡_) satisfies P for every pair of equal objects.
    --   The conclusion of the type (∀{x y : T} → (eq : (x ≡ y)) → P{x}{y}(eq)) means:
    --     Every identity proof satisfies P for every pair there is.
    --   In other words, to prove a proposition that depends on an identity proof, one only need to prove it for reflexivity.
    -- When joined by reflexivity, they become another characterization of equality.
    -- It is the elimination rule of the following data definition:
    --   data Id : T → T → Type{ℓ} where
    --     intro : ∀{x : T} → Id x x
    -- More information:
    -- • https://homotopytypetheory.org/2011/04/10/just-kidding-understanding-identity-elimination-in-homotopy-type-theory/
    -- • https://stackoverflow.com/questions/22580842/non-trivial-negation-in-agda
    IdentityEliminator : ∀{_} → Stmt
    IdentityEliminator{ℓₚ} = (P : ∀{x y : T} → (Id x y) → Stmt{ℓₚ}) → (∀{x : T} → P(reflexivity(Id) {x})) → (∀{x y : T} → (eq : (Id x y)) → P(eq))

    -- This looks similar to IdentityEliminator, but combined with reflexivity, it is able to prove that for any x, reflexivity of x is the only proof of (Id x x), also called the uniqueness of identity proofs (UIP).
    -- Also called: axiom K.
    -- More information:
    -- • https://homotopytypetheory.org/2011/04/10/just-kidding-understanding-identity-elimination-in-homotopy-type-theory/
    -- • Investigations Into Intensional Type Theory (Thomas Streicher, 1993) [https://www2.mathematik.tu-darmstadt.de/~streicher/HabilStreicher.pdf]
    -- • https://stackoverflow.com/questions/39239363/what-is-axiom-k
    IdentityKEliminator : ∀{_} → Stmt
    IdentityKEliminator{ℓₚ} = (P : ∀{x : T} → (Id x x) → Stmt{ℓₚ}) → (∀{x : T} → P(reflexivity(Id) {x})) → (∀{x : T} → (eq : (Id x x)) → P(eq))

    -- Elimination rule for identity types.
    -- Also called: J, j.
    -- There is a slight difference between this and IdentityEliminator. Here, the first parameter (x : T) is fixed throughout the whole definition.
    -- Some proofs are easier/more difficult to formulate using this variant. They can be proven equivalent.
    -- It is the elimination rule of the following data definition:
    --   data Id (x : T) : T → Type{ℓ} where
    --     intro : Id x x
    IdentityEliminatorAltₗ : ∀{_} → Stmt
    IdentityEliminatorAltₗ{ℓₚ} = ∀{y : T} → (P : ∀{x : T} → (Id x y) → Stmt{ℓₚ}) → P(reflexivity(Id) {y}) → (∀{x : T} → (eq : (Id x y)) → P(eq))
    IdentityEliminatorAltᵣ : ∀{_} → Stmt
    IdentityEliminatorAltᵣ{ℓₚ} = ∀{x : T} → (P : ∀{y : T} → (Id x y) → Stmt{ℓₚ}) → P(reflexivity(Id) {x}) → (∀{y : T} → (eq : (Id x y)) → P(eq))

    -- Usage of the trivial reflexivity proof can be substituted by any proof of the same type.
    -- Also called: axiom K.
    -- There is a slight difference between this and IdentityKEliminator. Here, the parameter of (x : T) is fixed throughout the whole definition.
    -- Some proofs are easier/more difficult to formulate using this variant. They can be proven equivalent.
    IdentityKEliminatorAlt : ∀{_} → Stmt
    IdentityKEliminatorAlt{ℓₚ} = ∀{x : T} → (P : (Id x x) → Stmt{ℓₚ}) → P(reflexivity(Id) {x}) → ((eq : (Id x x)) → P(eq))

module _ {ℓ ℓₑ} {T : Type{ℓ}} (Id : T → T → Stmt{ℓₑ}) ⦃ refl : Reflexivity(Id) ⦄ {ℓₚ} where
  record IdentityEliminator : Stmt{ℓ Lvl.⊔ ℓₑ Lvl.⊔ Lvl.𝐒(ℓₚ)} where
    constructor intro
    field elim : Names.IdentityEliminator(Id) {ℓₚ}
  idElim = inferArg IdentityEliminator.elim

  record IdentityKEliminator : Stmt{ℓ Lvl.⊔ ℓₑ Lvl.⊔ Lvl.𝐒(ℓₚ)} where
    constructor intro
    field elim : Names.IdentityKEliminator(Id) {ℓₚ}
  idKElim = inferArg IdentityKEliminator.elim

module _
  {ℓ ℓₚ ℓₑ ℓₚₑ}
  {T : Type{ℓ}}
  (Id : T → T → Type{ℓₑ}) ⦃ refl-T :  Reflexivity(Id) ⦄  ⦃ identElim-T : IdentityEliminator(Id) ⦄
  (P : ∀{x y : T} → (Id x y) → Stmt{ℓₚ})
  (_≡_ : ∀{x y : T}{xy : Id x y} → P(xy) → P(xy) → Type{ℓₚₑ})
  where

  open Reflexivity (refl-T) using () renaming (proof to refl)

  -- Reflexivity is an identity element for the identity elimination operation.
  record IdentityEliminationOfIntro : Stmt{ℓ Lvl.⊔ Lvl.𝐒(ℓₚ) Lvl.⊔ ℓₑ Lvl.⊔ ℓₚₑ} where
    constructor intro
    field proof : (p : ∀{x} → P{x}{x}(refl)) → (∀{x : T} → (idElim(Id)(P) p refl ≡ p{x}))
  idElimOfIntro = inferArg IdentityEliminationOfIntro.proof

module _
  {ℓ ℓₚ ℓₑ ℓₚₑ}
  {T : Type{ℓ}}
  (Id : T → T → Type{ℓₑ}) ⦃ refl-T :  Reflexivity(Id) ⦄  ⦃ identKElim-T : IdentityKEliminator(Id) ⦄
  (P : ∀{x y : T} → (Id x y) → Stmt{ℓₚ})
  (_≡_ : ∀{x y : T}{xy : Id x y} → P(xy) → P(xy) → Type{ℓₚₑ})
  where

  open Reflexivity (refl-T) using () renaming (proof to refl)

  record IdentityKEliminationOfIntro : Stmt{ℓ Lvl.⊔ Lvl.𝐒(ℓₚ) Lvl.⊔ ℓₑ Lvl.⊔ ℓₚₑ} where
    constructor intro
    field proof : (p : ∀{x} → P{x}{x}(refl)) → (∀{x : T} → (idKElim(Id)(P) p refl ≡ p{x}))
  idKElimOfIntro = inferArg IdentityKEliminationOfIntro.proof

module _ {ℓₑ : Lvl.Level → Lvl.Level} (Id : ∀{ℓ}{T : Type{ℓ}} → T → T → Stmt{ℓₑ(ℓ)}) where
  record IdentityType : Stmtω where
    constructor intro
    field
      ⦃ introduction-rule ⦄ : ∀{ℓ}{T : Type{ℓ}} → Reflexivity{T = T} Id
      ⦃ elimination-rule ⦄  : ∀{ℓ ℓₚ}{T : Type{ℓ}} → IdentityEliminator{T = T} Id {ℓₚ}
      ⦃ computation-rule ⦄  : ∀{ℓ ℓₚ}{T : Type{ℓ}}{P : ∀{x y : T} → (Id x y) → Stmt{ℓₚ}} → IdentityEliminationOfIntro{T = T} Id P Id
