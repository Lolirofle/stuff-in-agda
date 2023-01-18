{-# OPTIONS --cubical #-}

module Miscellaneous.FiniteMultiset2 where

import      Lvl
open import Functional as Fn using (_$_)
open import Type.Cubical.Path
open import Type.Cubical.Path.Equality
open import Type.Properties.Homotopy
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable x y z : T

data FiniteMultiset(T : Type{ℓ}) : Type{ℓ} where
  ∅ : FiniteMultiset(T)
  _•∪_ : T → FiniteMultiset(T) → FiniteMultiset(T)
  swap : ∀{x y}{s} → Path(x •∪ y •∪ s) (y •∪ x •∪ s)
  -- set : Names.HomotopyLevel(2) (FiniteMultiset(T))
pattern _∪•_ s x = _•∪_ x s
infixr 1000 _•∪_
infixl 1000 _∪•_

module _
  (P : FiniteMultiset(T) → Type{ℓ})
  (pe : P(∅))
  (ps : ∀{x}{s} → P(s) → P(x •∪ s))
  (pc : ∀{x y}{s} → (p : P(s)) → PathP(\i → P(swap{x = x}{y = y}{s = s} i)) (ps{x} (ps{y} p)) (ps{y} (ps{x} p)))
  where

  elim : (s : FiniteMultiset(T)) → P(s)
  elim ∅ = pe
  elim (x •∪ s) = ps{x}{s} (elim s)
  elim (swap{x}{y}{s} i) = pc{x}{y}{s} (elim s) i

module _ where
  open import Data.List as List using (List)

  fromList : List(T) → FiniteMultiset(T)
  fromList List.∅       = ∅
  fromList (x List.⊰ l) = x •∪ fromList(l)

  {- TODO: Requires a specific permutation of all lists so that (Path s₁ s₂) → ∃(s ↦ (s₁ permutes s) ∧ (s₂ permutes s)). For example using sorting: If s is the sorted list of s₁, then s is also the sorted list of s₂.
  list : FiniteMultiset(T) → {!!} → List(T)
  list ∅ p = List.∅
  list(x •∪ s) p = x List.⊰ list(s)
  list(swap i) p = {!!}

  fromListIntro : (P : FiniteMultiset(T) → Type{ℓ}) → ((l : List(T)) → P(fromList(l))) → ((s : FiniteMultiset(T)) → P(s))
  fromListIntro P p ∅ = p List.∅
  fromListIntro P p (x •∪ s) = {!p(x List.⊰ ?)!}
  fromListIntro P p (swap i) = {!!}
  -}

module _ where
  open import Data.Boolean
  open import Data.Boolean.Numeral
  import      Data.Boolean.Operators
  open        Data.Boolean.Operators.Programming
  open import Numeral.Natural

  _∪_ : FiniteMultiset(T) → FiniteMultiset(T) → FiniteMultiset(T)
  ∅         ∪ s₂ = s₂
  (x •∪ s₁) ∪ s₂ = x •∪ (s₁ ∪ s₂)
  (swap{x}{y}{s₁} i) ∪ s₂ = swap{x = x}{y = y}{s = s₁ ∪ s₂} i

  map : (A → B) → FiniteMultiset(A) → FiniteMultiset(B)
  map f ∅ = ∅
  map f(x •∪ s) = f(x) •∪ map f(s)
  map f(swap{x}{y}{s} i) = swap{x = f(x)}{y = f(y)}{s = map f(s)} i
  -- map f (set {x}{y} {p₁}{p₂} i j) = set{x = map f(x)}{y = map f(y)}{x = \j → map f(p₁ j)}{y = \j → map f(p₂ j)} i j

  satisfiesAny : (T → Bool) → FiniteMultiset(T) → Bool
  satisfiesAny f ∅ = 𝐹
  satisfiesAny f (x •∪ s) = f(x) || satisfiesAny f s
  satisfiesAny f (swap{x}{y}{s} i) with f(x) | f(y) | satisfiesAny f s
  ... | 𝑇 | 𝑇 | 𝑇 = 𝑇
  ... | 𝑇 | 𝑇 | 𝐹 = 𝑇
  ... | 𝑇 | 𝐹 | 𝑇 = 𝑇
  ... | 𝑇 | 𝐹 | 𝐹 = 𝑇
  ... | 𝐹 | 𝑇 | 𝑇 = 𝑇
  ... | 𝐹 | 𝑇 | 𝐹 = 𝑇
  ... | 𝐹 | 𝐹 | 𝑇 = 𝑇
  ... | 𝐹 | 𝐹 | 𝐹 = 𝐹
  {-applyₚₐₜₕ i $
    f x || (f y || satisfiesAny f s) 🝖[ Path ]-[ {!!} ]
    (f x || f y) || satisfiesAny f s 🝖[ Path ]-[ {!!} ]
    (f y || f x) || satisfiesAny f s 🝖[ Path ]-[ {!!} ]
    f y || (f x || satisfiesAny f s) 🝖-end
  -}

  count : (T → Bool) → FiniteMultiset(T) → ℕ
  count f ∅ = 𝟎
  count f (x •∪ s) = (if f(x) then 𝐒 else Fn.id) (count f s)
  count f (swap{x}{y}{s} i) with f(x) | f(y)
  ... | 𝑇 | 𝑇 = 𝐒(𝐒(count f s))
  ... | 𝑇 | 𝐹 = 𝐒(count f s)
  ... | 𝐹 | 𝑇 = 𝐒(count f s)
  ... | 𝐹 | 𝐹 = count f s

module _ where
  private variable P : T → Type{ℓ}
  private variable s s₁ s₂ : FiniteMultiset(T)

  data AllElements (P : T → Type{ℓ}) : FiniteMultiset(T) → Type{Lvl.of(T) Lvl.⊔ ℓ} where
    ∅ : AllElements P ∅
    _⊰_ : P(x) → AllElements P s → AllElements P (x •∪ s)
  ∀ₘₛₑₜ : FiniteMultiset(T) → (T → Type{ℓ}) → Type
  ∀ₘₛₑₜ(s) P = AllElements P s

  data ExistsElement (P : T → Type{ℓ}) : FiniteMultiset(T) → Type{Lvl.of(T) Lvl.⊔ ℓ} where
    • : P(x) → ExistsElement P (x •∪ s)
  ∃ₘₛₑₜ : FiniteMultiset(T) → (T → Type{ℓ}) → Type
  ∃ₘₛₑₜ(s) P = ExistsElement P s

  data _∈_ (x : T) : FiniteMultiset(T) → Type{Lvl.of(T)} where
    • : (x ∈ (x •∪ s))

  open import Structure.Relator

  [∃ₘₛₑₜ]-step : ∃ₘₛₑₜ(s) P → ∃ₘₛₑₜ(x •∪ s) P
  [∃ₘₛₑₜ]-step {P = P} (• p) = substitute₂-₁ᵣ(∃ₘₛₑₜ)(P) swap (• p)

  [∈]-step : (x ∈ s) → (x ∈ (y •∪ s))
  [∈]-step {x = x} • = substitute₂-₂ᵣ(_∈_)(x) swap •

  open import Structure.Function
  open import Structure.Operator
  open import Structure.Relator.Properties
  open import Syntax.Transitivity
  open import Type.Cubical.Path.Functions

  {- TODO: Maybe not possible. Probably why `set` is necessary
  test : Names.HomotopyLevel(2) (T) → Names.HomotopyLevel(2) (FiniteMultiset(T))
  test p {∅} {∅} {p₁} {p₂} i j = {!∅!}
  test p {∅} {x •∪ y} {p₁} {p₂} i j = {!!}
  test p {∅} {swap i₁} {p₁} {p₂} i j = {!!}
  test p {x •∪ x₁} {∅} {p₁} {p₂} i j = {!!}
  test p {x •∪ x₁} {x₂ •∪ y} {p₁} {p₂} i j = {!!}
  test p {x •∪ x₁} {swap i₁} {p₁} {p₂} i j = {!!}
  test p {swap i₁} {∅} {p₁} {p₂} i j = {!!}
  test p {swap i₁} {x •∪ y} {p₁} {p₂} i j = {!!}
  test p {swap i₁} {swap i₂} {p₁} {p₂} i j = {!!}
  -}

  [∪]-identityᵣ : Path(s ∪ ∅) s
  [∪]-identityᵣ {s = ∅} = reflexivity(Path)
  [∪]-identityᵣ {s = x •∪ s} = congruence₂-₂(_•∪_)(x) ([∪]-identityᵣ {s = s})
  [∪]-identityᵣ {s = swap{s = s} i} = mapP(\s → swap{s = s} i) ([∪]-identityᵣ {s = s})

  [•∪][∪]-commute : Path(x •∪ (s₁ ∪ s₂)) (s₁ ∪ (x •∪ s₂))
  [•∪][∪]-commute        {s₁ = ∅}                = reflexivity(Path)
  [•∪][∪]-commute {x = x}{s₁ = y •∪ s₁}{s₂ = s₂} = swap 🝖 congruence₂-₂(_•∪_)(y) ([•∪][∪]-commute {x = x}{s₁ = s₁}{s₂ = s₂})
  [•∪][∪]-commute {x = x}{s₁ = swap{a}{b}{s₁} i}{s₂ = s₂} = {!!}
  -- mapP(\s → swap{x = a}{y = b}{s = s} i) ([•∪][∪]-commute {x = x}{s₁ = s₁}{s₂ = s₂})
  -- ? 🝖 mapPᵢ(\i s → swap{x = a}{y = b}{s = s} i) ([•∪][∪]-commute {x = x}{s₁ = s}{s₂ = s₂})

  [∪]-commutativity : Path(s₁ ∪ s₂) (s₂ ∪ s₁)
  [∪]-commutativity {s₁ = ∅} {s₂ = s₂} = symmetry(Path) [∪]-identityᵣ
  [∪]-commutativity {s₁ = x •∪ s₁} {s₂ = s₂} = congruence₂-₂(_•∪_)(x) ([∪]-commutativity {s₁ = s₁}{s₂ = s₂}) 🝖 [•∪][∪]-commute {x = x}{s₁ = s₂}{s₂ = s₁}
  [∪]-commutativity {s₁ = swap i} {s₂ = s₂} = {![•∪][∪]-commute!}

-- test : Path(x •∪ x •∪ y •∪ z •∪ ∅) (y •∪ z •∪ x •∪ x •∪ ∅)
-- test = {!swap!}
