module Structure.Type.Identity.Proofs.Eliminator where

import      Lvl
open import Functional using (_→ᶠ_ ; id ; _on₂_ ; swap ; apply)
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Proofs.Structures
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Groupoid
open import Structure.Setoid using (Equiv ; intro) renaming (_≡_ to _≡ₛ_)
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Relator.Properties.Proofs
open import Structure.Relator
open import Structure.Type.Identity
open import Structure.Type.Identity.Proofs
open import Syntax.Function
open import Syntax.Transitivity
open import Syntax.Type
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂ ℓₑ ℓₘₑ ℓₚ ℓₒ : Lvl.Level
private variable T A B : Type{ℓ}
private variable x y : T
private variable Id _≡_ _▫_ : T → T → Stmt{ℓ}

module Oper (Id : T → T → Type{ℓₑ}) ⦃ refl :  Reflexivity(Id) ⦄ ⦃ identElim : IdentityEliminator{ℓₚ = ℓₑ}(Id) ⦄ where
  open Symmetry    (identity-eliminator-to-symmetry     {Id = Id}) using () renaming (proof to sym)   public
  open Transitivity(identity-eliminator-to-transitivity {Id = Id}) using () renaming (proof to trans) public
  ftrans = identity-eliminator-to-flipped-transitivityᵣ ⦃ refl ⦄ ⦃ identElim ⦄

module Oper2 (Id : A → A → Type{ℓₑ}) ⦃ refl :  Reflexivity(Id) ⦄ ⦃ identElim : IdentityEliminator{ℓₚ = ℓₚ}(Id) ⦄ where
  open Reflexivity (refl) using () renaming (proof to refl)  public
  module _ (_▫_ : A → A → Type{ℓₚ}) ⦃ [▫]-refl : Reflexivity(_▫_) ⦄ where
    open _⊆₂_ identity-eliminator-to-reflexive-subrelation using () renaming (proof to sub) public
  module _ (_▫_ : B → B → Type{ℓₚ}) ⦃ [▫]-refl : Reflexivity(_▫_) ⦄ (f : A → B) where
    open _⊆₂_ (minimal-reflection-transport ⦃ minRefl = identity-eliminator-to-reflexive-subrelation ⦄ {_▫_ = _▫_} {f = f}) using () renaming (proof to transp) public

module _
  {Id : T → T → Type{ℓₑ}} ⦃ refle-T :  Reflexivity(Id) ⦄  ⦃ identElim-T : IdentityEliminator(Id) ⦄
  {_≡_ : ∀{T : Type{ℓₑ}} → T → T → Type{ℓₘₑ}}
  ⦃ identElimOfIntro : IdentityEliminationOfIntro(Id)(_≡_) ⦄
  where

  open Oper(Id)
  open Oper2{ℓₚ = ℓₑ}(Id)

  identity-eliminator-symmetry-of-refl : ∀{x} → (sym refl ≡ refl{x})
  identity-eliminator-symmetry-of-refl = idElimOfIntro(Id)(_≡_) (\{x y} _ → (Id y x)) refl

module _
  {Id : T → T → Type{ℓₑ₁}} ⦃ refle-T :  Reflexivity(Id) ⦄  ⦃ identElim-T : IdentityEliminator(Id) ⦄
  {_≡_ : ∀{T : Type{ℓₑ₂}} → T → T → Type{ℓₘₑ}}
  ⦃ identElimOfIntro : IdentityEliminationOfIntro(Id)(_≡_) ⦄
  {_▫_ : T → T → Type{ℓₑ₂}} ⦃ refl-op : Reflexivity(_▫_) ⦄
  where

  open Oper(Id)
  open Oper2{ℓₚ = ℓₑ₂}(Id)

  identity-eliminator-reflexive-subrelation-of-refl : ∀{x} → (sub(_▫_) refl ≡ reflexivity(_▫_){x})
  identity-eliminator-reflexive-subrelation-of-refl = idElimOfIntro(Id)(_≡_) (\{x y} _ → (x ▫ y)) (reflexivity(_▫_))

module _
  {Id : A → A → Type{ℓₑ₁}} ⦃ refle-A :  Reflexivity(Id) ⦄  ⦃ identElim-A : IdentityEliminator(Id) ⦄
  {_≡_ : ∀{T : Type{ℓₑ₂}} → T → T → Type{ℓₘₑ}}
  ⦃ identElimOfIntro : IdentityEliminationOfIntro(Id)(_≡_) ⦄
  {_▫_ : B → B → Type{ℓₑ₂}} ⦃ refle-B : Reflexivity(_▫_) ⦄
  {f : A → B}
  where

  open Oper(Id)
  open Oper2{ℓₚ = ℓₑ₂}(Id)

  identity-eliminator-transport-of-refl : ∀{a} → (transp(_▫_)(f) (refl{a}) ≡ reflexivity(_▫_) {f(a)})
  identity-eliminator-transport-of-refl {a} = identity-eliminator-reflexive-subrelation-of-refl {_≡_ = _≡_} {_▫_ = (_▫_) on₂ f} ⦃ on₂-reflexivity ⦄ {x = a}

module _
  {Id : T → T → Type{ℓₑ}}
    ⦃ refle-T :  Reflexivity(Id) ⦄
    ⦃ identElim-T : IdentityEliminator(Id) ⦄
  {_≡_ : ∀{T : Type{ℓₑ}} → T → T → Type{ℓₘₑ}}
    ⦃ refle-eq : ∀{T : Type} → Reflexivity(_≡_ {T = T}) ⦄
    ⦃ identElim-eq : ∀{T : Type} → IdentityEliminator{ℓₚ = ℓₘₑ}(_≡_ {T = T}) ⦄
  ⦃ identElimOfIntro : IdentityEliminationOfIntro(Id)(_≡_) ⦄
  where

  open Oper(Id)
  open Oper2{ℓₚ = ℓₑ}(Id)
  instance _ = identity-eliminator-to-reflexive-subrelation

  identity-eliminator-flipped-transitivityᵣ-of-refl : ∀{x} → (ftrans refl refl ≡ refl{x})
  identity-eliminator-flipped-transitivityᵣ-of-refl {z} = sub₂(_≡_)((_≡_) on₂ (apply refl)) ⦃ minimal-reflection-transport ⦄ identity-eliminator-transport-of-refl

  identity-eliminator-transitivity-of-refl : ∀{x} → (trans refl refl ≡ refl{x})
  identity-eliminator-transitivity-of-refl = transitivity(_≡_) ⦃ identity-eliminator-to-transitivity ⦄ p identity-eliminator-flipped-transitivityᵣ-of-refl where
    p : trans refl refl ≡ ftrans refl refl
    p = sub₂(_≡_)((_≡_) on₂ (p ↦ identity-eliminator-to-flipped-transitivityᵣ p refl)) ⦃ minimal-reflection-transport ⦄ identity-eliminator-symmetry-of-refl    

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
    ⦃ identElim-A : IdentityEliminator(Equiv._≡_ equiv-A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {_≡_ : ∀{T : Type{ℓₑ₂}} → T → T → Type{ℓₘₑ}}
  ⦃ identElimOfIntro : IdentityEliminationOfIntro(Equiv._≡_ equiv-A)(_≡_) ⦄
  where

  open Reflexivity(Equiv.reflexivity equiv-A) using () renaming (proof to refl-A)
  open Reflexivity(Equiv.reflexivity equiv-B) using () renaming (proof to refl-B)
  instance _ = identity-eliminator-to-reflexive-subrelation
  instance _ = minimal-reflection-to-function

  identity-eliminator-function-of-refl : ∀{f : A → B}{a} → (congruence₁(f) (refl-A {a}) ≡ refl-B {f(a)})
  identity-eliminator-function-of-refl = identity-eliminator-transport-of-refl

module _
  ⦃ equiv-T : Equiv{ℓₑ₁}(T) ⦄
    ⦃ identElim-T : IdentityEliminator(Equiv._≡_ equiv-T) ⦄
  {_≡_ : ∀{T : Type{ℓₑ₂}} → T → T → Type{ℓₘₑ}}
    ⦃ refle-eq : ∀{T : Type} → Reflexivity(_≡_ {T = T}) ⦄
    ⦃ identElim-eq : ∀{T : Type} → IdentityEliminator{ℓₚ = ℓₘₑ}(_≡_ {T = T}) ⦄
  ⦃ identElimOfIntro : IdentityEliminationOfIntro(Equiv._≡_ equiv-T)(_≡_) ⦄
  where

  open Reflexivity(Equiv.reflexivity equiv-T) using () renaming (proof to refl)
  instance _ = identity-eliminator-to-reflexive-subrelation
  instance _ = minimal-reflection-to-relator

  identity-eliminator-relator-of-refl : ∀{P : T → Stmt}{x}{p : P(x)} → (substitute₁ᵣ(P) refl p ≡ p)
  identity-eliminator-relator-of-refl {p = p} = sub₂(_≡_)((_≡_) on₂ (apply p)) ⦃ minimal-reflection-transport ⦄ identity-eliminator-transport-of-refl
module _
  {Id : T → T → Type{ℓₑ}}
    ⦃ refle-T :  Reflexivity(Id) ⦄
    ⦃ identElim-T : ∀{ℓₚ} → IdentityEliminator{ℓₚ = ℓₚ}(Id) ⦄
    -- ⦃ identElim₁-T : IdentityEliminator{ℓₚ = ℓₑ}(Id) ⦄
    -- ⦃ identElim₂-T : IdentityEliminator{ℓₚ = ℓₘₑ}(Id) ⦄
    -- ⦃ identElim₃-T : IdentityEliminator{ℓₚ = ℓₑ Lvl.⊔ ℓₘₑ}(Id) ⦄
  {_≡_ : ∀{T : Type{ℓₑ}} → T → T → Type{ℓₘₑ}}
    ⦃ refle-eq : ∀{T : Type} → Reflexivity(_≡_ {T = T}) ⦄
    ⦃ identElim-eq : ∀{T : Type} → IdentityEliminator{ℓₚ = ℓₘₑ}(_≡_ {T = T}) ⦄ -- TODO: Try to not have these and instead have the properties that are used
  ⦃ identElimOfIntro : IdentityEliminationOfIntro(Id)(_≡_) ⦄
  where

  open Reflexivity (refle-T)                                       using () renaming (proof to refl)
  open Symmetry    (identity-eliminator-to-symmetry     {Id = Id}) using () renaming (proof to sym)
  open Transitivity(identity-eliminator-to-transitivity {Id = Id}) using () renaming (proof to trans)
  instance _ = identity-eliminator-to-reflexive-subrelation
  instance _ = \{T} → identity-eliminator-to-symmetry     {Id = _≡_ {T = T}} ⦃ refl = refle-eq ⦄ ⦃ identElim = identElim-eq ⦄
  instance _ = \{T} → identity-eliminator-to-transitivity {Id = _≡_ {T = T}} ⦃ refl = refle-eq ⦄ ⦃ identElim = identElim-eq ⦄
  instance _ = \{T} → Structure.Setoid.intro(_) ⦃ identity-eliminator-to-equivalence {Id = _≡_ {T = T}} ⦃ refl = refle-eq ⦄ ⦃ identElim = identElim-eq ⦄ ⦄

  identity-eliminator-identityₗ : ∀{x y}{p : Id x y} → (trans refl p ≡ p)
  identity-eliminator-identityₗ {p = p} = idElim(Id) (p ↦ (trans refl p ≡ p)) identity-eliminator-transitivity-of-refl p

  identity-eliminator-identityᵣ : ∀{x y}{p : Id x y} → (trans p refl ≡ p)
  identity-eliminator-identityᵣ {p = p} = idElim(Id) (p ↦ (trans p refl ≡ p)) identity-eliminator-transitivity-of-refl p

  identity-eliminator-associativity : ∀{x y z w}{p : Id x y}{q : Id y z}{r : Id z w} → (trans (trans p q) r ≡ trans p (trans q r))
  identity-eliminator-associativity {p = p} {q = q} {r = r} =
    idElim(Id)
      (p ↦ ∀ q r → (trans (trans p q) r ≡ trans p (trans q r)))
      (q ↦ r ↦ (
        trans (trans refl q) r 🝖[ _≡_ ]-[ sub₂(_≡_)((_≡_) on₂ (expr ↦ trans expr r)) ⦃ identity-eliminator-to-reflexive-subrelation ⦃ refl = on₂-reflexivity ⦄ ⦄ identity-eliminator-identityₗ ]
        trans q r              🝖[ _≡_ ]-[ identity-eliminator-identityₗ ]-sym
        trans refl (trans q r) 🝖-end
      ))
      p q r

  identity-eliminator-inverseₗ : ∀{x y}{p : Id x y} → (trans (sym p) p ≡ refl)
  identity-eliminator-inverseₗ {p = p} =
    idElim(Id)
      (p ↦ trans (sym p) p ≡ refl)
      (
        trans (sym refl) refl 🝖[ _≡_ ]-[ identity-eliminator-identityᵣ ]
        sym refl              🝖[ _≡_ ]-[ identity-eliminator-symmetry-of-refl ]
        refl                  🝖-end
      )
      p

  identity-eliminator-inverseᵣ : ∀{x y}{p : Id x y} → (trans p (sym p) ≡ refl)
  identity-eliminator-inverseᵣ {p = p} =
    idElim(Id)
      (p ↦ trans p (sym p) ≡ refl)
      (
        trans refl (sym refl) 🝖[ _≡_ ]-[ identity-eliminator-identityₗ ]
        sym refl              🝖[ _≡_ ]-[ identity-eliminator-symmetry-of-refl ]
        refl                  🝖-end
      )
      p

  identity-eliminator-categorical-identityₗ : Morphism.Identityₗ{Obj = T} (\{x} → swap(trans{x})) (refl)
  identity-eliminator-categorical-identityₗ = Morphism.intro identity-eliminator-identityᵣ

  identity-eliminator-categorical-identityᵣ : Morphism.Identityᵣ{Obj = T} (\{x} → swap(trans{x})) (refl)
  identity-eliminator-categorical-identityᵣ = Morphism.intro identity-eliminator-identityₗ

  identity-eliminator-categorical-identity : Morphism.Identity{Obj = T} (\{x} → swap(trans{x})) (refl)
  identity-eliminator-categorical-identity = [∧]-intro identity-eliminator-categorical-identityₗ identity-eliminator-categorical-identityᵣ

  identity-eliminator-categorical-associativity : Morphism.Associativity{Obj = T} (\{x} → swap(trans{x}))
  identity-eliminator-categorical-associativity = Morphism.intro (symmetry(_≡_) identity-eliminator-associativity)

  identity-eliminator-categorical-inverterₗ : Polymorphism.Inverterₗ{Obj = T} (\{x} → swap(trans{x})) (refl) (sym)
  identity-eliminator-categorical-inverterₗ = Polymorphism.intro identity-eliminator-inverseᵣ

  identity-eliminator-categorical-inverterᵣ : Polymorphism.Inverterᵣ{Obj = T} (\{x} → swap(trans{x})) (refl) (sym)
  identity-eliminator-categorical-inverterᵣ = Polymorphism.intro identity-eliminator-inverseₗ

  identity-eliminator-categorical-inverter : Polymorphism.Inverter{Obj = T} (\{x} → swap(trans{x})) (refl) (sym)
  identity-eliminator-categorical-inverter = [∧]-intro identity-eliminator-categorical-inverterₗ identity-eliminator-categorical-inverterᵣ

  identity-eliminator-groupoid : Groupoid(Id)
  Groupoid._∘_ identity-eliminator-groupoid = swap(trans)
  Groupoid.id  identity-eliminator-groupoid = refl
  Groupoid.inv identity-eliminator-groupoid = sym
  Groupoid.associativity  identity-eliminator-groupoid = identity-eliminator-categorical-associativity
  Groupoid.identity       identity-eliminator-groupoid = identity-eliminator-categorical-identity
  Groupoid.inverter       identity-eliminator-groupoid = identity-eliminator-categorical-inverter
  Groupoid.binaryOperator identity-eliminator-groupoid = intro a where postulate a : ∀{a} → a -- TODO
