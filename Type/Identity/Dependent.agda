module Type.Identity.Dependent where

import      Lvl
open import Type
open import Type.Identity as Id using (Id ; intro)

private variable ℓ ℓᵢ ℓₚ : Lvl.Level

data DId {ℓᵢ ℓ} {I : Type{ℓᵢ}}{T : I → Type{ℓ}} : ∀{a b} → .(Id a b) → T(a) → T(b) → Type{ℓ Lvl.⊔ ℓᵢ} where
  instance intro : ∀{i}{x : T(i)} → DId intro x x

module _
  {I : Type{ℓᵢ}}
  {T : I → Type{ℓ}}
  (P : ∀{a b}.{id : Id a b}{ta : T(a)}{tb : T(b)} → DId id ta tb → Type{ℓₚ})
  (p : ∀{a}{t : T(a)} → P{id = intro}{ta = t}{tb = t} intro)
  where

  elim : ∀{a b}.{id : Id a b}{ta : T(a)}{tb : T(b)} → (deq : DId id ta tb) → P deq
  elim intro = p

module _
  {I : Type{ℓᵢ}}
  {T : I → Type{ℓ}}
  {b} {tb : T(b)}
  (P : ∀{a}.{id : Id a b}{ta : T(a)} → DId id ta tb → Type{ℓₚ})
  (p : P{id = intro}{ta = tb} intro)
  where

  elimAltₗ : ∀{a}.{id : Id a b}{ta : T(a)} → (deq : DId id ta tb) → P deq
  elimAltₗ intro = p

module _
  {I : Type{ℓᵢ}}
  {T : I → Type{ℓ}}
  {a} {ta : T(a)}
  (P : ∀{b}.{id : Id a b}{tb : T(b)} → DId id ta tb → Type{ℓₚ})
  (p : P{id = intro}{tb = ta} intro)
  where

  elimAltᵣ : ∀{b}.{id : Id a b}{tb : T(b)} → (deq : DId id ta tb) → P deq
  elimAltᵣ intro = p



import Functional as Fn

private variable I : Type{ℓᵢ}
private variable T : I → Type{ℓ}
private variable a b c x : I

Id-sub : (P : I → I → Type{ℓ}) → (∀{x} → P x x) → ∀{a b} → Id a b → P a b
Id-sub P = Id.elim(\{x}{y} _ → P x y)

Id-sym : Id a b → Id b a
Id-sym = Id-sub(Fn.swap Id) intro

Id-trans : Id a b → Id b c → Id a c
Id-trans = Fn.swap(Id-sub(\b c → Id _ b → Id _ c) Fn.id)

sub : (P : ∀{a b} → .(id : Id a b) → (ta : T(a)) → (tb : T(b)) → Type{ℓₚ}) → (∀{a}{t : T(a)} → P intro t t) → ∀{a b}.{id : Id a b}{ta : T(a)}{tb : T(b)} → DId id ta tb → P id ta tb
sub P = elim(\{a}{b}{id}{ta}{tb} _ → P{a}{b} id ta tb)

subₗ : ∀{b}{tb : T(b)} → (P : ∀{a} → .(id : Id a b) → (ta : T(a)) → Type{ℓₚ}) → P intro tb → ∀{a}.{id : Id a b}{ta : T(a)} → DId id ta tb → P id ta
subₗ P = elimAltₗ(\{a}{id}{ta} _ → P{a} id ta)

subᵣ : ∀{a}{ta : T(a)} → (P : ∀{b} → .(id : Id a b) → (tb : T(b)) → Type{ℓₚ}) → P intro ta → ∀{b}.{id : Id a b}{tb : T(b)} → DId id ta tb → P id tb
subᵣ P = elimAltᵣ(\{b}{id}{tb} _ → P{b} id tb)

substᵣ : (P : ∀{x} → T(x) → Type{ℓₚ}) → ∀{a b}.{id : Id a b}{ta : T(a)}{tb : T(b)} → DId id ta tb → P(ta) → P(tb)
substᵣ P eq = sub(\_ ta tb → P(ta) →  P(tb)) Fn.id eq

sym : ∀.{id : Id a b}{ta : T(a)}{tb : T(b)} → DId id ta tb → DId (Id-sym id) tb ta
sym = sub(\id ta tb → DId (Id-sym id) tb ta) intro

trans : ∀.{id₁ : Id a b}.{id₂ : Id b c}{ta : T(a)}{tb : T(b)}{tc : T(c)} → DId id₁ ta tb → DId id₂ tb tc → DId (Id-trans id₁ id₂) ta tc
trans {a = a}{ta = ta} ab bc = sub(\{b}{c} id₂ tb tc → ∀.{id₁ : Id a b} → DId id₁ ta tb → DId(Id-trans id₁ id₂) ta tc) Fn.id bc ab

Id-to-DId-const : ∀{t₁ t₂ : I} → (id : Id t₁ t₂) → DId{T = Fn.const(I)} id t₁ t₂
Id-to-DId-const intro = intro

Id-to-DId : ∀{t₁ t₂ : T x}{id : Id x x} → Id t₁ t₂ → DId{T = T} id t₁ t₂
Id-to-DId intro = intro

DId-const-to-Id : ∀{T : Type{ℓ}}{a b : I}{ta tb : T}{id : Id a b} → DId{T = Fn.const T} id ta tb → Id ta tb
DId-const-to-Id intro = intro

-- DId-to-Id : ∀{ta tb : T(x)}{id : Id x x} → DId{T = T} id ta tb → Id ta tb
-- DId-to-Id {T = T}{x = x}{ta = ta}{tb = tb}{id = id} eq = {!substᵣ(\t → )!}

propIndex : ∀{id : Id a b}{pa : T(a)}{pb : T(b)} → (∀{x}{t₁ t₂ : T(x)} → DId intro t₁ t₂) → DId id pa pb
propIndex {id = id}{pa = pa}{pb = pb} prop = Id.elim(\eq → ∀{pa}{pb} → DId eq pa pb) (\{x}{pa}{pb} → prop{x}{pa}{pb}) id {pa}{pb}

-- propIndex' : ∀{id : Id a b}{pa : T(a)}{pb : T(b)} → (∀{x}{t₁ t₂ : T(x)} → Id t₁ t₂) → DId id pa pb
-- propIndex'{id = id} prop = propIndex{id = id} \{x}{t₁}{t₂} → IdToDId'{x = x}{t₁}{t₂} prop {intro}
