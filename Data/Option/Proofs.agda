module Data.Option.Proofs where

import      Lvl
open import Data
open import Data.Option
open import Data.Option.Equiv
open import Data.Option.Functions
open import Functional
open import Structure.Setoid using (Equiv)
open import Structure.Function.Domain
open import Structure.Function
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable x y : T
private variable o : Option(T)

module _ where
  open import Function.Equals
  open        Structure.Setoid

  module _ ⦃ _ : let _ = A ; _ = B ; _ = C in Equiv{ℓₑ}(C) ⦄ {f : B → C}{g : A → B} {c : C} where
    partialMap-map-[∘] : (partialMap c (f ∘ g) ⊜ (partialMap c f ∘ map g))
    _⊜_.proof partialMap-map-[∘] {None}   = reflexivity(_≡_)
    _⊜_.proof partialMap-map-[∘] {Some _} = reflexivity(_≡_)

  module _ ⦃ _ : let _ = A ; _ = B ; _ = C in Equiv{ℓₑ}(C) ⦄ {f : B → C}{g : A → B} {b : B} where
    partialMap-apply-compose : ((partialMap (f $ b) (f ∘ g)) ⊜ (f ∘ partialMap b g))
    _⊜_.proof partialMap-apply-compose {None}   = reflexivity(_≡_)
    _⊜_.proof partialMap-apply-compose {Some _} = reflexivity(_≡_)

  module _
    ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
    ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
    ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄
    ⦃ equiv-oA : Equiv{ℓₑ₄}(Option(A)) ⦄
    ⦃ ext-A : Extensionality(equiv-oA) ⦄
    {b₁ b₂ : B}
    {f₁ f₂ : A → B}
    ⦃ func-f₂ : Function(f₂) ⦄
    where

    open Extensionality(ext-A)

    partialMap-function : ∀{o₁ o₂} → (b₁ ≡ b₂) → (f₁ ⊜ f₂) → (o₁ ≡ o₂) → (partialMap b₁ f₁ o₁ ≡ partialMap b₂ f₂ o₂)
    partialMap-function {o₁ = None}   {o₂ = None}   pb pf po = pb
    partialMap-function {o₁ = None}   {o₂ = Some y} pb pf po with () ← cases-inequality po
    partialMap-function {o₁ = Some x} {o₂ = None}   pb pf po with () ← cases-inequality (symmetry(_≡_) po)
    partialMap-function {o₁ = Some x} {o₂ = Some y} pb pf po = _⊜_.proof pf 🝖 congruence₁(f₂) (injective(Some) po)

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
    andThenᵣ-None : o andThen (const(None{T = A})) ≡ None
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
    andCombine-associativity : ⦃ _ : Associativity(_▫_) ⦄ → Associativity(andCombine(_▫_))
    andCombine-associativity = intro (\{x}{y}{z} → p{x}{y}{z}) where
      p : Names.Associativity(andCombine(_▫_))
      p {None}   {None}   {None}   = reflexivity(_≡_)
      p {None}   {None}   {Some _} = reflexivity(_≡_)
      p {None}   {Some _} {None}   = reflexivity(_≡_)
      p {None}   {Some _} {Some _} = reflexivity(_≡_)
      p {Some _} {None}   {None}   = reflexivity(_≡_)
      p {Some _} {None}   {Some _} = reflexivity(_≡_)
      p {Some _} {Some _} {None}   = reflexivity(_≡_)
      p {Some _} {Some _} {Some _} = congruence₁(Some) (associativity(_▫_))

  module _ where
    orCombine-associativity : ∀{f} ⦃ idemp-f : Idempotent(f) ⦄ (_ : ∀{x y} → (f(x) ▫ y ≡ f(x ▫ y))) (_ : ∀{x y} → (x ▫ f(y) ≡ f(x ▫ y))) → ⦃ _ : Associativity(_▫_) ⦄ → Associativity(orCombine(_▫_) f f) -- TODO: What are the unnamed properties here in the assumptions called? Also, the constant function of an absorber have all these properties. The identity function also have it.
    orCombine-associativity {f = f} compatₗ compatᵣ = intro (\{x}{y}{z} → p{x}{y}{z}) where
      p : Names.Associativity(orCombine(_▫_) f f)
      p {None}   {None}   {None}   = reflexivity(_≡_)
      p {None}   {None}   {Some z} = congruence₁(Some) (symmetry(_≡_) (idempotent(f)))
      p {None}   {Some y} {None}   = reflexivity(_≡_)
      p {None}   {Some y} {Some z} = congruence₁(Some) compatₗ
      p {Some x} {None}   {None}   = congruence₁(Some) (idempotent(f))
      p {Some x} {None}   {Some z} = congruence₁(Some) (transitivity(_≡_) compatₗ (symmetry(_≡_) compatᵣ))
      p {Some x} {Some y} {None}   = congruence₁(Some) (symmetry(_≡_) compatᵣ)
      p {Some x} {Some y} {Some z} = congruence₁(Some) (associativity(_▫_))

module _
  ⦃ equiv-A  : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B  : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-oA : Equiv{ℓₑ₃}(Option(A)) ⦄
  ⦃ equiv-oB : Equiv{ℓₑ₄}(Option(B)) ⦄
  ⦃ ext-B : Extensionality(equiv-oB) ⦄
  {f : A → B}
  where

  open import Logic.Predicate
  open import Logic.Propositional
  open Structure.Setoid

  open Extensionality(ext-B)

  map-Some-value : (map f(o) ≡ Some y) → ∃(x ↦ (f(x) ≡ y) ∧ (o ≡ Some(x)))
  map-Some-value {o = None}   eq with () ← cases-inequality eq
  map-Some-value {o = Some x} eq = [∃]-intro x ⦃ [∧]-intro (injective(Some) eq) (reflexivity(_≡_)) ⦄
