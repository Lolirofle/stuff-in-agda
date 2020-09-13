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
open import Structure.Setoid.WithLvl using (Equiv ; intro) renaming (_≡_ to _≡ₛ_)
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
private variable _≡_ _▫_ : T → T → Stmt{ℓ}

{- TODO: Old stuff
module _ {ℓₑ : Lvl.Level → Lvl.Level}{_≡_ : ∀{ℓ}{T : Type{ℓ}} → T → T → Stmt{ℓₑ(ℓ)}} ⦃ ident : IdentityType(_≡_) ⦄ where
  open import Structure.Categorical.Properties

  open IdentityType(ident)
  private
    instance
      eq-equiv : ∀{x y : T} → Equiv(x ≡ y)
      eq-equiv = intro(_≡_) ⦃ identity-eliminator-to-equivalence ⦄

  identity-proof-identityₗ : ∀{x y : T} → Morphism.Identityₗ{Obj = x ≡ y}(\{x} → swap(transitivity(_≡_) {x}))(reflexivity(_≡_))
  Morphism.Identityₗ.proof (identity-proof-identityₗ {x = x} {y = y}) {xy₁} {xy₂} {xy₁xy₂} = elim-of-intro (xy ↦ {!!}) {!!}
  -- elim-of-intro{T = x ≡ y} (xy ↦ (swap(transitivity(_≡_)) (reflexivity(_≡_)) xy ≡ xy)) {!!}
-}

module _
  {_≡_ : T → T → Type{ℓₑ}} ⦃ refle-T :  Reflexivity(_≡_) ⦄  ⦃ identElim-T : IdentityEliminator(_≡_) ⦄
  {_≡ₘ_ : ∀{T : Type{ℓₑ}} → T → T → Type{ℓₘₑ}}
  ⦃ identElimOfIntro : IdentityEliminationOfIntro{_≡_ = _≡_}{_≡ₘ_ = _≡ₘ_} ⦄
  where

  open Reflexivity (refle-T)                                     using () renaming (proof to refl)
  open Symmetry    (identity-eliminator-to-symmetry {_≡_ = _≡_}) using () renaming (proof to sym)

  identity-eliminator-symmetry-of-refl : ∀{x} → (sym refl ≡ₘ refl{x})
  identity-eliminator-symmetry-of-refl = idElimOfIntro (\{x y} _ → (y ≡ x)) refl

module _
  {_≡_ : T → T → Type{ℓₑ₁}} ⦃ refle-T :  Reflexivity(_≡_) ⦄  ⦃ identElim-T : IdentityEliminator(_≡_) ⦄
  {_≡ₘ_ : ∀{T : Type{ℓₑ₂}} → T → T → Type{ℓₘₑ}}
  ⦃ identElimOfIntro : IdentityEliminationOfIntro{_≡_ = _≡_}{_≡ₘ_ = _≡ₘ_} ⦄
  {_▫_ : T → T → Type{ℓₑ₂}} ⦃ refl-op : Reflexivity(_▫_) ⦄
  where

  open Reflexivity (refle-T) using () renaming (proof to refl)

  identity-eliminator-reflexive-subrelation-of-refl : ∀{x} → _⊆₂_.proof (identity-eliminator-to-reflexive-subrelation {_≡_ = _≡_}{_▫_ = _▫_}) refl ≡ₘ reflexivity(_▫_){x}
  identity-eliminator-reflexive-subrelation-of-refl = idElimOfIntro (\{x y} _ → (x ▫ y)) (reflexivity(_▫_))

module _
  {_≡_ : A → A → Type{ℓₑ₁}} ⦃ refle-A :  Reflexivity(_≡_) ⦄  ⦃ identElim-A : IdentityEliminator(_≡_) ⦄
  {_≡ₘ_ : ∀{T : Type{ℓₑ₂}} → T → T → Type{ℓₘₑ}}
  ⦃ identElimOfIntro : IdentityEliminationOfIntro{_≡_ = _≡_}{_≡ₘ_ = _≡ₘ_} ⦄
  {_▫_ : B → B → Type{ℓₑ₂}} ⦃ refle-B : Reflexivity(_▫_) ⦄
  {f : A → B}
  where

  identity-eliminator-transport-of-refl : ∀{a} → (_⊆₂_.proof (minimal-reflection-transport ⦃ minRefl = identity-eliminator-to-reflexive-subrelation ⦄ {_▫_ = _▫_} {f = f}) (reflexivity(_≡_) {a}) ≡ₘ reflexivity(_▫_) {f(a)})
  identity-eliminator-transport-of-refl {a} = identity-eliminator-reflexive-subrelation-of-refl {_≡ₘ_ = _≡ₘ_} {_▫_ = (_▫_) on₂ f} ⦃ on₂-reflexivity ⦄ {x = a}

module _
  {_≡_ : T → T → Type{ℓₑ}}
    ⦃ refle-T :  Reflexivity(_≡_) ⦄
    ⦃ identElim-T : IdentityEliminator(_≡_) ⦄
  {_≡ₘ_ : ∀{T : Type{ℓₑ}} → T → T → Type{ℓₘₑ}}
    ⦃ refle-eq : ∀{T : Type} → Reflexivity(_≡ₘ_ {T = T}) ⦄
    ⦃ identElim-eq : ∀{T : Type} → IdentityEliminator{ℓₚ = ℓₘₑ}(_≡ₘ_ {T = T}) ⦄
  ⦃ identElimOfIntro : IdentityEliminationOfIntro{_≡_ = _≡_}{_≡ₘ_ = _≡ₘ_} ⦄
  where

  open Reflexivity (refle-T)                                         using () renaming (proof to refl)
  open Symmetry    (identity-eliminator-to-symmetry     {_≡_ = _≡_}) using () renaming (proof to sym)
  open Transitivity(identity-eliminator-to-transitivity {_≡_ = _≡_}) using () renaming (proof to trans)
  instance _ = identity-eliminator-to-reflexive-subrelation

  identity-eliminator-flipped-transitivityᵣ-of-refl : ∀{x} → (identity-eliminator-to-flipped-transitivityᵣ refl refl ≡ₘ refl{x})
  identity-eliminator-flipped-transitivityᵣ-of-refl {z} = sub₂(_≡ₘ_)((_≡ₘ_) on₂ (apply refl)) ⦃ minimal-reflection-transport ⦄ identity-eliminator-transport-of-refl

  identity-eliminator-transitivity-of-refl : ∀{x} → (trans refl refl ≡ₘ refl{x})
  identity-eliminator-transitivity-of-refl = transitivity(_≡ₘ_) ⦃ identity-eliminator-to-transitivity ⦄ p identity-eliminator-flipped-transitivityᵣ-of-refl where
    p : trans refl refl ≡ₘ identity-eliminator-to-flipped-transitivityᵣ refl refl
    p = sub₂(_≡ₘ_)((_≡ₘ_) on₂ (p ↦ identity-eliminator-to-flipped-transitivityᵣ p refl)) ⦃ minimal-reflection-transport ⦄ identity-eliminator-symmetry-of-refl    

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
    ⦃ identElim-A : IdentityEliminator(Equiv._≡_ equiv-A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {_≡ₘ_ : ∀{T : Type{ℓₑ₂}} → T → T → Type{ℓₘₑ}}
  ⦃ identElimOfIntro : IdentityEliminationOfIntro{_≡_ = Equiv._≡_ equiv-A}{_≡ₘ_ = _≡ₘ_} ⦄
  where

  open Reflexivity(Equiv.reflexivity equiv-A) using () renaming (proof to refl-A)
  open Reflexivity(Equiv.reflexivity equiv-B) using () renaming (proof to refl-B)
  instance _ = identity-eliminator-to-reflexive-subrelation
  instance _ = minimal-reflection-to-function

  identity-eliminator-function-of-refl : ∀{f : A → B}{a} → (congruence₁(f) (refl-A {a}) ≡ₘ refl-B {f(a)})
  identity-eliminator-function-of-refl = identity-eliminator-transport-of-refl

module _
  ⦃ equiv-T : Equiv{ℓₑ₁}(T) ⦄
    ⦃ identElim-T : IdentityEliminator(Equiv._≡_ equiv-T) ⦄
  {_≡ₘ_ : ∀{T : Type{ℓₑ₂}} → T → T → Type{ℓₘₑ}}
    ⦃ refle-eq : ∀{T : Type} → Reflexivity(_≡ₘ_ {T = T}) ⦄
    ⦃ identElim-eq : ∀{T : Type} → IdentityEliminator{ℓₚ = ℓₘₑ}(_≡ₘ_ {T = T}) ⦄
  ⦃ identElimOfIntro : IdentityEliminationOfIntro{_≡_ = Equiv._≡_ equiv-T}{_≡ₘ_ = _≡ₘ_} ⦄
  where

  open Reflexivity(Equiv.reflexivity equiv-T) using () renaming (proof to refl)
  instance _ = identity-eliminator-to-reflexive-subrelation
  instance _ = minimal-reflection-to-relator

  identity-eliminator-relator-of-refl : ∀{P : T → Stmt}{x}{p : P(x)} → (substitute₁(P) refl p ≡ₘ p)
  identity-eliminator-relator-of-refl {p = p} = sub₂(_≡ₘ_)((_≡ₘ_) on₂ (apply p)) ⦃ minimal-reflection-transport ⦄ identity-eliminator-transport-of-refl
module _
  {_≡_ : T → T → Type{ℓₑ}}
    ⦃ refle-T :  Reflexivity(_≡_) ⦄
    ⦃ identElim-T : ∀{ℓₚ} → IdentityEliminator{ℓₚ = ℓₚ}(_≡_) ⦄
    -- ⦃ identElim₁-T : IdentityEliminator{ℓₚ = ℓₑ}(_≡_) ⦄
    -- ⦃ identElim₂-T : IdentityEliminator{ℓₚ = ℓₘₑ}(_≡_) ⦄
    -- ⦃ identElim₃-T : IdentityEliminator{ℓₚ = ℓₑ Lvl.⊔ ℓₘₑ}(_≡_) ⦄
  {_≡ₘ_ : ∀{T : Type{ℓₑ}} → T → T → Type{ℓₘₑ}}
    ⦃ refle-eq : ∀{T : Type} → Reflexivity(_≡ₘ_ {T = T}) ⦄
    ⦃ identElim-eq : ∀{T : Type} → IdentityEliminator{ℓₚ = ℓₘₑ}(_≡ₘ_ {T = T}) ⦄
  ⦃ identElimOfIntro : IdentityEliminationOfIntro{_≡_ = _≡_}{_≡ₘ_ = _≡ₘ_} ⦄
  where

  open Reflexivity (refle-T)                                         using () renaming (proof to refl)
  open Symmetry    (identity-eliminator-to-symmetry     {_≡_ = _≡_}) using () renaming (proof to sym)
  open Transitivity(identity-eliminator-to-transitivity {_≡_ = _≡_}) using () renaming (proof to trans)
  instance _ = identity-eliminator-to-reflexive-subrelation
  instance _ = \{T} → identity-eliminator-to-symmetry     {_≡_ = _≡ₘ_ {T = T}} ⦃ refle = refle-eq ⦄ ⦃ identElim = identElim-eq ⦄
  instance _ = \{T} → identity-eliminator-to-transitivity {_≡_ = _≡ₘ_ {T = T}} ⦃ refle = refle-eq ⦄ ⦃ identElim = identElim-eq ⦄
  instance _ = \{T} → Structure.Setoid.WithLvl.intro(_) ⦃ identity-eliminator-to-equivalence {_≡_ = _≡ₘ_ {T = T}} ⦃ refle = refle-eq ⦄ ⦃ identElim = identElim-eq ⦄ ⦄

  identity-eliminator-identityₗ : ∀{x y}{p : x ≡ y} → (trans refl p ≡ₘ p)
  identity-eliminator-identityₗ {p = p} = idElim(_≡_) (p ↦ (trans refl p ≡ₘ p)) identity-eliminator-transitivity-of-refl p

  identity-eliminator-identityᵣ : ∀{x y}{p : x ≡ y} → (trans p refl ≡ₘ p)
  identity-eliminator-identityᵣ {p = p} = idElim(_≡_) (p ↦ (trans p refl ≡ₘ p)) identity-eliminator-transitivity-of-refl p

  identity-eliminator-associativity : ∀{x y z w}{p : x ≡ y}{q : y ≡ z}{r : z ≡ w} → (trans (trans p q) r ≡ₘ trans p (trans q r))
  identity-eliminator-associativity {p = p} {q = q} {r = r} =
    idElim(_≡_)
      (p ↦ ∀ q r → (trans (trans p q) r ≡ₘ trans p (trans q r)))
      (q ↦ r ↦ (
        trans (trans refl q) r 🝖[ _≡ₘ_ ]-[ sub₂(_≡ₘ_)((_≡ₘ_) on₂ (expr ↦ trans expr r)) ⦃ identity-eliminator-to-reflexive-subrelation ⦃ refl = on₂-reflexivity ⦄ ⦄ identity-eliminator-identityₗ ]
        trans q r              🝖[ _≡ₘ_ ]-[ identity-eliminator-identityₗ ]-sym
        trans refl (trans q r) 🝖-end
      ))
      p q r

  identity-eliminator-inverseₗ : ∀{x y}{p : x ≡ y} → (trans (sym p) p ≡ₘ refl)
  identity-eliminator-inverseₗ {p = p} =
    idElim(_≡_)
      (p ↦ trans (sym p) p ≡ₘ refl)
      (
        trans (sym refl) refl 🝖[ _≡ₘ_ ]-[ identity-eliminator-identityᵣ ]
        sym refl              🝖[ _≡ₘ_ ]-[ identity-eliminator-symmetry-of-refl ]
        refl                  🝖-end
      )
      p

  identity-eliminator-inverseᵣ : ∀{x y}{p : x ≡ y} → (trans p (sym p) ≡ₘ refl)
  identity-eliminator-inverseᵣ {p = p} =
    idElim(_≡_)
      (p ↦ trans p (sym p) ≡ₘ refl)
      (
        trans refl (sym refl) 🝖[ _≡ₘ_ ]-[ identity-eliminator-identityₗ ]
        sym refl              🝖[ _≡ₘ_ ]-[ identity-eliminator-symmetry-of-refl ]
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
  identity-eliminator-categorical-associativity = Morphism.intro (symmetry(_≡ₘ_) identity-eliminator-associativity)

  identity-eliminator-categorical-inverterₗ : Polymorphism.Inverterₗ{Obj = T} (\{x} → swap(trans{x})) (refl) (sym)
  identity-eliminator-categorical-inverterₗ = Polymorphism.intro identity-eliminator-inverseᵣ

  identity-eliminator-categorical-inverterᵣ : Polymorphism.Inverterᵣ{Obj = T} (\{x} → swap(trans{x})) (refl) (sym)
  identity-eliminator-categorical-inverterᵣ = Polymorphism.intro identity-eliminator-inverseₗ

  identity-eliminator-categorical-inverter : Polymorphism.Inverter{Obj = T} (\{x} → swap(trans{x})) (refl) (sym)
  identity-eliminator-categorical-inverter = [∧]-intro identity-eliminator-categorical-inverterₗ identity-eliminator-categorical-inverterᵣ

  identity-eliminator-groupoid : Groupoid(_≡_)
  Groupoid._∘_ identity-eliminator-groupoid = swap(trans)
  Groupoid.id  identity-eliminator-groupoid = refl
  Groupoid.inv identity-eliminator-groupoid = sym
  Groupoid.associativity  identity-eliminator-groupoid = identity-eliminator-categorical-associativity
  Groupoid.identity       identity-eliminator-groupoid = identity-eliminator-categorical-identity
  Groupoid.inverter       identity-eliminator-groupoid = identity-eliminator-categorical-inverter
  Groupoid.binaryOperator identity-eliminator-groupoid = intro a where postulate a : ∀{a} → a -- TODO
