module Data.Option.Proofs where

import      Lvl
open import Data
open import Data.Option
open import Data.Option.Equiv using (Extensionality)
open import Data.Option.Functions
open import Data.Option.Relation
open import Functional as Fn using (_∘_ ; _$_ ; const)
open import Function.EqualsRaw
open import Function.Proofs
open import Logic.Predicate
open import Logic.Propositional
open import Structure.Setoid using (Equiv)
open import Structure.Function
open import Structure.Function.Domain
import      Structure.Function.Names as Names
open import Structure.Operator
open import Structure.Operator.Monoid
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ ℓₑₒ₁ ℓₑₒ₂ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable x y id : T
private variable o : Option(T)

module _ where
  open        Structure.Setoid

  module _ ⦃ _ : let _ = A ; _ = B ; _ = C in Equiv{ℓₑ}(C) ⦄ {f : B → C}{g : A → B} {c : C} where
    partialMap-map-[∘] : (partialMap c (f ∘ g) ⊜ (partialMap c f ∘ map g))
    partialMap-map-[∘] {None}   = reflexivity(_≡_)
    partialMap-map-[∘] {Some _} = reflexivity(_≡_)

  module _ ⦃ _ : let _ = A ; _ = B ; _ = C in Equiv{ℓₑ}(C) ⦄ {f : B → C}{g : A → B} {b : B} where
    partialMap-apply-compose : ((partialMap (f $ b) (f ∘ g)) ⊜ (f ∘ partialMap b g))
    partialMap-apply-compose {None}   = reflexivity(_≡_)
    partialMap-apply-compose {Some _} = reflexivity(_≡_)

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
    partialMap-function {o₁ = Some x} {o₂ = Some y} pb pf po = pf 🝖 congruence₁(f₂) (injective(Some) po)

  module _ ⦃ _ : let _ = A ; _ = B ; _ = C in Equiv{ℓₑ}(Option(C)) ⦄ {f : B → C}{g : A → B} where
    map-preserves-[∘] : (map(f ∘ g) ⊜ (map f) ∘ (map g))
    map-preserves-[∘] {None}   = reflexivity(_≡_)
    map-preserves-[∘] {Some x} = reflexivity(_≡_)

  module _ ⦃ _ : Equiv{ℓₑ}(Option(A)) ⦄ where
    map-preserves-id : (map Fn.id ⊜ Fn.id)
    map-preserves-id {None}   = reflexivity(_≡_)
    map-preserves-id {Some x} = reflexivity(_≡_)

    andThenᵣ-Some : ((_andThen Some) ⊜ Fn.id)
    andThenᵣ-Some {None}   = reflexivity(_≡_)
    andThenᵣ-Some {Some x} = reflexivity(_≡_)

  module _ ⦃ _ : Equiv{ℓₑ}(Option(A)) ⦄ where
    andThenᵣ-None : o andThen (const None) ≡ None
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

module _
  {_▫_ : T → T → T}
  ⦃ equiv-T : Equiv{ℓₑ}(T) ⦄
  ⦃ equiv-opt-T : Equiv{ℓₑ₂}(Option(T)) ⦄
  where

  open Structure.Setoid

  instance
    andCombine-absorberₗ : Absorberₗ(andCombine(_▫_))(None)
    Absorberₗ.proof andCombine-absorberₗ {None}   = reflexivity(_≡_)
    Absorberₗ.proof andCombine-absorberₗ {Some x} = reflexivity(_≡_)

  instance
    andCombine-absorberᵣ : Absorberᵣ(andCombine(_▫_))(None)
    Absorberᵣ.proof andCombine-absorberᵣ {None}   = reflexivity(_≡_)
    Absorberᵣ.proof andCombine-absorberᵣ {Some x} = reflexivity(_≡_)

  -- `andCombine` essentially adds an additional value (None) to the type, and it becomes an absorber by definition.
  instance
    andCombine-absorber : Absorber(andCombine(_▫_))(None)
    andCombine-absorber = intro

  instance
    orCombine-identityₗ : ∀{l} → Identityₗ(orCombine(_▫_) l Fn.id)(None)
    Identityₗ.proof orCombine-identityₗ {None} = reflexivity(_≡_)
    Identityₗ.proof orCombine-identityₗ {Some x} = reflexivity(_≡_)

  instance
    orCombine-identityᵣ : ∀{r} → Identityᵣ(orCombine(_▫_) Fn.id r)(None)
    Identityᵣ.proof orCombine-identityᵣ {None} = reflexivity(_≡_)
    Identityᵣ.proof orCombine-identityᵣ {Some x} = reflexivity(_≡_)

  instance
    orCombine-identity : Identity(orCombine(_▫_) Fn.id Fn.id)(None)
    orCombine-identity = intro

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

  instance
    andCombine-identityₗ : ⦃ ident : Identityₗ(_▫_)(id) ⦄ → Identityₗ(andCombine(_▫_))(Some(id))
    Identityₗ.proof andCombine-identityₗ {None} = reflexivity(_≡_)
    Identityₗ.proof (andCombine-identityₗ {id = id}) {Some x} = congruence₁(Some) (identityₗ(_▫_)(id))

  instance
    andCombine-identityᵣ : ⦃ ident : Identityᵣ(_▫_)(id) ⦄ → Identityᵣ(andCombine(_▫_))(Some(id))
    Identityᵣ.proof andCombine-identityᵣ {None} = reflexivity(_≡_)
    Identityᵣ.proof (andCombine-identityᵣ {id = id}) {Some x} = congruence₁(Some) (identityᵣ(_▫_)(id))

  instance
    andCombine-identity : ⦃ ident : Identity(_▫_)(id) ⦄ → Identity(andCombine(_▫_))(Some(id))
    andCombine-identity = intro

  -- Note: The constant function using an absorber satisfies all the properties. The identity function also do.
  orCombine-associativity : ∀{f} ⦃ idemp-f : Idempotent(f) ⦄ (_ : ∀{x y} → (f(x) ▫ y ≡ f(x ▫ y))) (_ : ∀{x y} → (x ▫ f(y) ≡ f(x ▫ y))) → ⦃ _ : Associativity(_▫_) ⦄ → Associativity(orCombine(_▫_) f f) -- TODO: What are the unnamed properties here in the assumptions called? Also, 
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
  ⦃ equiv : Equiv{ℓₑ₁}(T) ⦄
  ⦃ equiv-Option : Equiv{ℓₑ₂}(Option(T)) ⦄
  ⦃ ext : Extensionality(equiv-Option) ⦄
  {_▫_ : T → T → T}
  ⦃ oper : BinaryOperator(_▫_) ⦄
  where

  open Extensionality(ext)
  open Monoid ⦃ … ⦄ using () renaming (id to idₘ)
  open Structure.Setoid

  instance
    andCombine-function : BinaryOperator(andCombine(_▫_))
    {-# CATCHALL #-}
    BinaryOperator.congruence andCombine-function {_}     {_}     {None}  {Some _} p₁ p₂ with () ← cases-inequality p₂
    {-# CATCHALL #-}
    BinaryOperator.congruence andCombine-function {_}     {_}     {Some _}{None}   p₁ p₂ with () ← cases-inequality (symmetry(_≡_) p₂)
    {-# CATCHALL #-}
    BinaryOperator.congruence andCombine-function {None}  {Some _}{_}     {_}      p₁ p₂ with () ← cases-inequality p₁
    {-# CATCHALL #-}
    BinaryOperator.congruence andCombine-function {Some _}{None}  {_}     {_}      p₁ p₂ with () ← cases-inequality (symmetry(_≡_) p₁)
    BinaryOperator.congruence andCombine-function {None}  {None}  {None}  {None}   p₁ p₂ = reflexivity(_≡_)
    BinaryOperator.congruence andCombine-function {Some a}{Some b}{None}  {None}   p₁ p₂ = reflexivity(_≡_)
    BinaryOperator.congruence andCombine-function {None}  {None}  {Some c}{Some d} p₁ p₂ = reflexivity(_≡_)
    BinaryOperator.congruence andCombine-function {Some a}{Some b}{Some c}{Some d} p₁ p₂ = congruence₁(Some) (congruence₂(_▫_) (injective(Some) p₁) (injective(Some) p₂))

  module _  {l r} ⦃ func-l : Function(l) ⦄ ⦃ func-r : Function(r) ⦄ where
    instance
      orCombine-function : BinaryOperator(orCombine(_▫_) l r)
      {-# CATCHALL #-}
      BinaryOperator.congruence orCombine-function {_}     {_}     {None}  {Some _} p₁ p₂ with () ← cases-inequality p₂
      {-# CATCHALL #-}
      BinaryOperator.congruence orCombine-function {_}     {_}     {Some _}{None}   p₁ p₂ with () ← cases-inequality (symmetry(_≡_) p₂)
      {-# CATCHALL #-}
      BinaryOperator.congruence orCombine-function {None}  {Some _}{_}     {_}      p₁ p₂ with () ← cases-inequality p₁
      {-# CATCHALL #-}
      BinaryOperator.congruence orCombine-function {Some _}{None}  {_}     {_}      p₁ p₂ with () ← cases-inequality (symmetry(_≡_) p₁)
      BinaryOperator.congruence orCombine-function {None}  {None}  {None}  {None}   p₁ p₂ = reflexivity(_≡_)
      BinaryOperator.congruence orCombine-function {Some a}{Some b}{None}  {None}   p₁ p₂ = congruence₁(Some) (congruence₁(l) (injective(Some) p₁))
      BinaryOperator.congruence orCombine-function {None}  {None}  {Some c}{Some d} p₁ p₂ = congruence₁(Some) (congruence₁(r) (injective(Some) p₂))
      BinaryOperator.congruence orCombine-function {Some a}{Some b}{Some c}{Some d} p₁ p₂ = congruence₁(Some) (congruence₂(_▫_) (injective(Some) p₁) (injective(Some) p₂))

  -- A monoid is constructed by lifting an associative binary operator using `orCombine`.
    -- Essentially means that an additional value (None) is added to the type, and it becomes an identity by definition.
  instance
    orCombine-monoid : ⦃ assoc : Associativity(_▫_) ⦄ → Monoid(orCombine(_▫_) Fn.id Fn.id)
    Monoid.associativity orCombine-monoid = orCombine-associativity (reflexivity(_≡_)) (reflexivity(_≡_))
    Monoid.identity-existence orCombine-monoid = [∃]-intro None

  -- A monoid is still a monoid when lifting a binary operator using `andCombine`.
  instance
    andCombine-monoid : ⦃ monoid : Monoid(_▫_) ⦄ → Monoid(andCombine(_▫_))
    Monoid.associativity andCombine-monoid = andCombine-associativity
    Monoid.identity-existence andCombine-monoid = [∃]-intro (Some(idₘ))

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

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-opt-A : Equiv{ℓₑₒ₁}(Option(A)) ⦄
  ⦃ ext-A : Extensionality equiv-opt-A ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-opt-B : Equiv{ℓₑₒ₂}(Option(B)) ⦄
  ⦃ ext-B : Extensionality equiv-opt-B ⦄
  where

  open Data.Option.Equiv
  open Structure.Setoid

  map-injective : ∀{f : A → B} ⦃ inj-f : Injective(f) ⦄ → Injective(map f)
  map-injective{f = f} = intro p where
    p : Names.Injective(map f)
    p {None}  {None}   xy = reflexivity(_≡_)
    p {None}  {Some y} xy = [⊥]-elim (cases-inequality xy)
    p {Some x}{None}   xy = [⊥]-elim (cases-inequality (symmetry(_≡_) xy))
    p {Some x}{Some y} xy = congruence₁(Some) (injective(f) (injective(Some) xy))

module _ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
  open Structure.Setoid

  partialMap-some-value : ∀{def}{f : A → B}{o} → ⦃ some : IsSome(o) ⦄ → (partialMap def f o ≡ f(extract o))
  partialMap-some-value {o = Some _} = reflexivity(_≡_)

  partialMap-none-value : ∀{def}{f : A → B}{o} → ⦃ none : IsNone(o) ⦄ → (partialMap def f o ≡ def)
  partialMap-none-value {o = None} = reflexivity(_≡_)

module _ ⦃ equiv-opt-B : Equiv{ℓₑₒ₂}(Option(B)) ⦄ where
  open Structure.Setoid

  map-some-value : ∀{f : A → B}{o} → ⦃ some : IsSome(o) ⦄ → (map f(o) ≡ Some(f(extract o)))
  map-some-value{o = o} = partialMap-some-value {o = o}

map-is-some : ∀{f : A → B}{o} → ⦃ some : IsSome(o) ⦄ → IsSome(map f(o))
map-is-some{o = Some _} = <>

map-is-none : ∀{f : A → B}{o} → ⦃ none : IsNone(o) ⦄ → IsNone(map f(o))
map-is-none{o = None} = <>

module _ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
  open Structure.Setoid

  extract-map : ∀{f : A → B}{o} ⦃ some : IsSome(o) ⦄ → (extract(map f(o)) ⦃ map-is-some ⦃ some ⦄ ⦄ ≡ f(extract o))
  extract-map {o = Some _} = reflexivity(_≡_)

module _
  ⦃ equiv : Equiv{ℓₑ₁}(T) ⦄
  ⦃ equiv-o : Equiv{ℓₑ₂}(Option(T)) ⦄
  ⦃ ext : Extensionality(equiv-o) ⦄
  where

  open Structure.Setoid

  extract-injective : ∀{o₁ o₂ : Option(T)} ⦃ some-o₁ : IsSome o₁ ⦄ ⦃ some-o₂ : IsSome o₂ ⦄ → (extract o₁ ≡ extract o₂) → (o₁ ≡ o₂)
  extract-injective {Some _}{Some _} = congruence₁(Some)

module _
  {ℓ₁ ℓ₂}
  {A : Type{ℓ₁}}
  {B : Option A → Type{ℓ₂}}
  {b}{ab}
  (P : {o : Option A} → B(o) → Type{ℓ})
  (pn : P b)
  (ps : {a : A} → P(ab a))
  where

  elim-intro : P{o} (elim{B = B} b ab o)
  elim-intro {o} = elim{B = \o → P{o} (elim{B = B} b ab o)} pn (\a → ps{a}) o

module _
  {def}{f : A → B}
  (P : {Option A} → B → Type{ℓ})
  (pn : P def)
  (ps : ∀{a} → P(f(a)))
  where

  partialMap-intro : P{o}(partialMap def f o)
  partialMap-intro = elim-intro (\{o} → P{o}) pn ps
