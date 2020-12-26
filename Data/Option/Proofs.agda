module Data.Option.Proofs where

import      Lvl
open import Data
open import Data.Option
open import Data.Option.Functions
open import Data.Either
open import Functional
open import Structure.Setoid using (Equiv)
open import Structure.Function.Domain
open import Structure.Function
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable x : T
private variable o : Option(T)

module _ where
  open Structure.Setoid
  open import Function.Equals

  module _ ⦃ _ : let _ = A ; _ = B ; _ = C in Equiv{ℓₑ}(Option(C)) ⦄ {f : B → C}{g : A → B} where
    map-preserves-[∘] : (map(f ∘ g) ⊜ (map f) ∘ (map g))
    _⊜_.proof map-preserves-[∘] {None}   = reflexivity(_≡_)
    _⊜_.proof map-preserves-[∘] {Some x} = reflexivity(_≡_)

  module _ ⦃ _ : Equiv{ℓₑ}(Option(A)) ⦄ where
    map-preserves-id : (map id ⊜ id)
    _⊜_.proof map-preserves-id {None}   = reflexivity(_≡_)
    _⊜_.proof map-preserves-id {Some x} = reflexivity(_≡_)

    andThenᵣ-Some : ((_andThen Some) ⊜ id)
    _⊜_.proof andThenᵣ-Some {None}   = reflexivity(_≡_)
    _⊜_.proof andThenᵣ-Some {Some x} = reflexivity(_≡_)

  module _ ⦃ _ : Equiv{ℓₑ}(Option(A)) ⦄ where
    andThenᵣ-None : o andThen (const{Y = Option(A)} None) ≡ None
    andThenᵣ-None {o = None}   = reflexivity(_≡_)
    andThenᵣ-None {o = Some x} = reflexivity(_≡_)

  module _ ⦃ _ : let _ = A in Equiv{ℓₑ}(Option(B)) ⦄ {f : A → Option(B)} where
    andThenₗ-None : (None andThen f ≡ None)
    andThenₗ-None = reflexivity(_≡_)

    andThenₗ-Some : (Some(x) andThen f ≡ f(x))
    andThenₗ-Some = reflexivity(_≡_)

  module _ ⦃ _ : let _ = A ; _ = B in Equiv{ℓₑ}(Option(C)) ⦄ {f : A → Option(B)} {g : B → Option(C)} where
    andThen-associativity : (o andThen (p ↦ f(p) andThen g) ≡ (o andThen f) andThen g)
    andThen-associativity {None}   = reflexivity(_≡_)
    andThen-associativity {Some x} = reflexivity(_≡_)

module _ where
  open import Function.Equals

  module _ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ ⦃ equiv-option-B : Equiv{ℓₑ}(Option B) ⦄ ⦃ some-func : Function(Some) ⦄  where
    map-function : Function(map {T₁ = A}{T₂ = B})
    Dependent._⊜_.proof (Function.congruence map-function (Dependent.intro p)) {None}   = reflexivity _
    Dependent._⊜_.proof (Function.congruence map-function (Dependent.intro p)) {Some x} = congruence₁(Some) p

  module _ ⦃ equiv-option-B : Equiv{ℓₑ}(Option B) ⦄ where
    andThen-function : Function(Functional.swap(_andThen_ {T₁ = A}{T₂ = B}))
    Dependent._⊜_.proof (Function.congruence andThen-function {f} {g} _)                   {None}   = reflexivity _
    Dependent._⊜_.proof (Function.congruence andThen-function {f} {g} (Dependent.intro p)) {Some x} = p{x}

module _
  ⦃ equiv-T     : Equiv{ℓₑ₁}(T) ⦄
  ⦃ equiv-opt-T : Equiv{ℓₑ₂}(Option(T)) ⦄
  ⦃ some-func   : Function(Some) ⦄
  {_▫_ : T → T → T}
  where

  open Structure.Setoid

  instance
    and-combine-associativity : ⦃ _ : Associativity(_▫_) ⦄ → Associativity(and-combine(_▫_))
    and-combine-associativity = intro p where
      p : Names.Associativity(and-combine(_▫_))
      p {None}   {None}   {None}   = reflexivity(_≡_)
      p {None}   {None}   {Some _} = reflexivity(_≡_)
      p {None}   {Some _} {None}   = reflexivity(_≡_)
      p {None}   {Some _} {Some _} = reflexivity(_≡_)
      p {Some _} {None}   {None}   = reflexivity(_≡_)
      p {Some _} {None}   {Some _} = reflexivity(_≡_)
      p {Some _} {Some _} {None}   = reflexivity(_≡_)
      p {Some _} {Some _} {Some _} = congruence₁(Some) (associativity(_▫_))

  module _ where --instance
    or-combine-associativity : ∀{f} ⦃ idemp-f : Idempotent(f) ⦄ (_ : ∀{x y} → (f(x) ▫ y ≡ f(x ▫ y))) (_ : ∀{x y} → (x ▫ f(y) ≡ f(x ▫ y))) → ⦃ _ : Associativity(_▫_) ⦄ → Associativity(or-combine(_▫_) f f) -- TODO: What are the unnamed properties here in the assumptions called? Also, the constant function of an absorber have all these properties. The identity function also have it.
    or-combine-associativity {f = f} compatₗ compatᵣ = intro p where
      p : Names.Associativity(or-combine(_▫_) f f)
      p {None}   {None}   {None}   = reflexivity(_≡_)
      p {None}   {None}   {Some z} = congruence₁(Some) (symmetry(_≡_) (idempotent(f)))
      p {None}   {Some y} {None}   = reflexivity(_≡_)
      p {None}   {Some y} {Some z} = congruence₁(Some) compatₗ
      p {Some x} {None}   {None}   = congruence₁(Some) (idempotent(f))
      p {Some x} {None}   {Some z} = congruence₁(Some) (transitivity(_≡_) compatₗ (symmetry(_≡_) compatᵣ))
      p {Some x} {Some y} {None}   = congruence₁(Some) (symmetry(_≡_) compatᵣ)
      p {Some x} {Some y} {Some z} = congruence₁(Some) (associativity(_▫_))
