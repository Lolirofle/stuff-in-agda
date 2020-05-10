module Data.Option.Proofs where

import      Lvl
open import Data
open import Data.Option
open import Data.Either
open import Data.Either.Proofs
open import Functional
open import Structure.Setoid using (Equiv)
open import Structure.Function.Domain
open import Structure.Function using (Function)
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Type

private variable ℓ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable x : T
private variable o : Option(T)

module _ where
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equiv

  Some-injectivity : Injective {B = Option(T)} (Some)
  Some-injectivity = Right-injectivity

module _ where
  open Structure.Setoid
  open import Function.Equals

  module _ ⦃ _ : let _ = A ; _ = B ; _ = C in Equiv(Option(C)) ⦄ {f : B → C}{g : A → B} where
    map-preserves-[∘] : (map(f ∘ g) ⊜ (map f) ∘ (map g))
    _⊜_.proof map-preserves-[∘] {None}   = reflexivity(_≡_)
    _⊜_.proof map-preserves-[∘] {Some x} = reflexivity(_≡_)

  module _ ⦃ _ : Equiv(Option(A)) ⦄ where
    map-preserves-id : (map id ⊜ id)
    _⊜_.proof map-preserves-id {None}   = reflexivity(_≡_)
    _⊜_.proof map-preserves-id {Some x} = reflexivity(_≡_)

    andThenᵣ-Some : ((_andThen Some) ⊜ id)
    _⊜_.proof andThenᵣ-Some {None}   = reflexivity(_≡_)
    _⊜_.proof andThenᵣ-Some {Some x} = reflexivity(_≡_)

  module _ ⦃ _ : Equiv(Option(A)) ⦄ where
    andThenᵣ-None : o andThen (const{Y = Option(A)} None) ≡ None
    andThenᵣ-None {o = None}   = reflexivity(_≡_)
    andThenᵣ-None {o = Some x} = reflexivity(_≡_)

  module _ ⦃ _ : let _ = A in Equiv(Option(B)) ⦄ {f : A → Option(B)} where
    andThenₗ-None : (None andThen f ≡ None)
    andThenₗ-None = reflexivity(_≡_)

    andThenₗ-Some : (Some(x) andThen f ≡ f(x))
    andThenₗ-Some = reflexivity(_≡_)

  module _ ⦃ _ : let _ = A ; _ = B in Equiv(Option(C)) ⦄ {f : A → Option(B)} {g : B → Option(C)} where
    andThen-associativity : (o andThen (p ↦ f(p) andThen g) ≡ (o andThen f) andThen g)
    andThen-associativity {None}   = reflexivity(_≡_)
    andThen-associativity {Some x} = reflexivity(_≡_)

module _ where
  open import Data.Either.Equiv
  open import Data.Proofs
  open import Function.Equals
  open import Relator.Equals

  module _ ⦃ equiv-B : Equiv(B) ⦄ where
    map-function-equiv : Function(map {T₁ = A}{T₂ = B})
    Dependent._⊜_.proof (Function.congruence map-function-equiv (Dependent.intro p)) {None}   = Left [≡]-intro
    Dependent._⊜_.proof (Function.congruence map-function-equiv (Dependent.intro p)) {Some x} = Right p

module _ where
  open import Function.Equals
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equiv

  map-function-eq : Function ⦃ [⊜]-equiv ⦄ ⦃ [⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄ (map {T₁ = A}{T₂ = B})
  Dependent._⊜_.proof (Function.congruence map-function-eq (Dependent.intro p)) {None}   = [≡]-intro
  Dependent._⊜_.proof (Function.congruence map-function-eq (Dependent.intro p)) {Some x} = [≡]-with(Some) p

  andThen-function-eq : Function ⦃ [⊜]-equiv ⦄ ⦃ [⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄ (Functional.swap(_andThen_ {T₁ = A}{T₂ = B}))
  Dependent._⊜_.proof (Function.congruence andThen-function-eq {f} {g} _)                   {None}   = [≡]-intro
  Dependent._⊜_.proof (Function.congruence andThen-function-eq {f} {g} (Dependent.intro p)) {Some x} = p{x}

{-
module _
  ⦃ _ : ∀{T : Type{ℓ}} → Equiv(T) ⦄
  ⦃ _ : ∀{T : Type{ℓ}} → Equiv(Option(T)) ⦄
  ⦃ _ : Function(Some) ⦄
  {_▫_ : ∀{T₁ T₂ T₃ : Type{ℓ}} → T₁ → T₂ → T₃}
  where

  open        Structure.Setoid
  open import Structure.Category
  open import Structure.Category.Properties

{-
  module _ (assoc : Names.Associativity(_▫_)) where
    or-combine-associativity-raw : Names.Associativity(or-combine(_▫_))
    or-combine-associativity-raw {None}   {None}   {None}   = reflexivity(_≡_)
    or-combine-associativity-raw {None}   {None}   {Some _} = reflexivity(_≡_)
    or-combine-associativity-raw {None}   {Some _} {None}   = reflexivity(_≡_)
    or-combine-associativity-raw {None}   {Some _} {Some _} = reflexivity(_≡_)
    or-combine-associativity-raw {Some _} {None}   {None}   = reflexivity(_≡_)
    or-combine-associativity-raw {Some _} {None}   {Some _} = reflexivity(_≡_)
    or-combine-associativity-raw {Some _} {Some _} {None}   = reflexivity(_≡_)
    or-combine-associativity-raw {Some _} {Some _} {Some _} = congruence₁(Some) assoc

  instance
    or-combine-associativity : ⦃ _ : Associativity(_▫_) ⦄ → Associativity(or-combine(_▫_))
    or-combine-associativity = intro(or-combine-associativity-raw(associativity(_▫_)))
-}

  module _ ⦃ assoc : Morphism.Associativity{Obj = Type{ℓ}}(_▫_) ⦄ where
    instance
      and-combine-associativity : Morphism.Associativity{Obj = Type{ℓ}} (and-combine(_▫_))
      {-Morphism.Associativity.proof and-combine-associativity {_}{_}{_}{_} {Left x} {Left x₁} {Left x₂} = reflexivity(_≡_)
      Morphism.Associativity.proof and-combine-associativity {_}{_}{_}{_} {Left x} {Left x₁} {Some x₂} = reflexivity(_≡_)
      Morphism.Associativity.proof and-combine-associativity {_}{_}{_}{_} {Left x} {Some x₁} {Left x₂} = reflexivity(_≡_)
      Morphism.Associativity.proof and-combine-associativity {_}{_}{_}{_} {Left x} {Some x₁} {Some x₂} = reflexivity(_≡_)
      Morphism.Associativity.proof and-combine-associativity {_}{_}{_}{_} {Some x} {Left x₁} {Left x₂} = reflexivity(_≡_)
      Morphism.Associativity.proof and-combine-associativity {_}{_}{_}{_} {Some x} {Left x₁} {Some x₂} = reflexivity(_≡_)
      Morphism.Associativity.proof and-combine-associativity {_}{_}{_}{_} {Some x} {Some x₁} {Left x₂} = reflexivity(_≡_)
      Morphism.Associativity.proof and-combine-associativity {X}{Y}{Z}{W} {Some x} {Some x₁} {Some x₂} = {!!} -- congruence₁(Some) (Morphism.associativity(_▫_) {x = X}{y = Y}{z = Z}{w = W})
-}
  module _ {id : T} where
    module _ ⦃ identₗ : Morphism.Identityₗ{Obj = Type{ℓ}}(_▫_)(id) ⦄ where
      instance
        and-combine-identityₗ : Morphism.Identityₗ{Obj = Type{ℓ}} (and-combine(_▫_))(Some id)
        Morphism.Identityₗ.proof and-combine-identityₗ {_}{_} {None}   = reflexivity(_≡_)
        Morphism.Identityₗ.proof and-combine-identityₗ {X}{Y} {Some x} = congruence₁(Some) (Morphism.identityₗ(_▫_)(id) {x = X}{y = Y})

    module _ ⦃ identᵣ : Morphism.Identityᵣ{Obj = Type{ℓ}}(_▫_)(id) ⦄ where
      instance
        and-combine-identityᵣ : Morphism.Identityᵣ{Obj = Type{ℓ}}(and-combine(_▫_))(Some id)
        Morphism.Identityᵣ.proof and-combine-identityᵣ {_}{_} {None}   = reflexivity(_≡_)
        Morphism.Identityᵣ.proof and-combine-identityᵣ {X}{Y} {Some x} = congruence₁(Some) (Morphism.identityᵣ(_▫_)(id) {x = X}{y = Y})

  module _
    ⦃ morphism-equiv : ∀{x y} → Equiv(x →ᶠ y) ⦄
    ⦃ cat : Category{Obj = Type{ℓ}}(_→ᶠ_) ⦄
    where

    and-combine-category : Category{Obj = Type{ℓ}}(_) -- ((_→ᶠ_) on₂ Option)
    Category._∘_ and-combine-category = {!and-combine!}
    Category.id and-combine-category = {!Some(Category.id (cat))!}
    Category.binaryOperator and-combine-category = {!!}
    Category.associativity and-combine-category = {!!}
    Category.identity and-combine-category = {!!}
-}
