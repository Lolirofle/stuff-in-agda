module Data.List.Relation.Membership.Proofs where

import Lvl
open import Functional
open import Data.List
open import Data.List.Functions hiding (skip)
open import Data.List.Relation.Membership
open import Data.List.Relation.Quantification
open import Data.List.Relation.Quantification.Proofs
open import Logic
open import Logic.Propositional
open import Numeral.Natural
open import Structure.Function
open import Structure.Relator.Properties
open import Structure.Setoid renaming (_≡_ to _≡ₛ_)
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable T A B : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  private variable l l₁ l₂ : List(T)
  private variable a b c x : T

  [∈]-self : AllElements(_∈ l)(l)
  [∈]-self {∅}     = ∅
  [∈]-self {x ⊰ l} = (• reflexivity(_≡ₛ_)) ⊰ AllElements-fn (⊰_) ([∈]-self {l})

  [∉]-empty : (a ∉ ∅)
  [∉]-empty ()

  [∈]-singleton : (a ∈ singleton(a))
  [∈]-singleton = use(reflexivity(_≡ₛ_))

  [∈]-singleton-[≡] : (a ∈ singleton(b)) → (a ≡ₛ b)
  [∈]-singleton-[≡] (use p) = p
  [∈]-singleton-[≡] (skip ())

  [∈][++] : (a ∈ (l₁ ++ l₂)) ↔ ((a ∈ l₁) ∨ (a ∈ l₂))
  [∈][++] = [↔]-intro L R where
    L : (a ∈ (l₁ ++ l₂)) ← ((a ∈ l₁) ∨ (a ∈ l₂))
    L {l₁ = ∅}      ([∨]-introᵣ p)     = p
    L {l₁ = x ⊰ l₁} ([∨]-introₗ (• p)) = • p
    L {l₁ = x ⊰ l₁} ([∨]-introₗ (⊰ p)) = ⊰ L {l₁ = l₁} ([∨]-introₗ p)
    L {l₁ = x ⊰ l₁} ([∨]-introᵣ p)     = ⊰ L {l₁ = l₁} ([∨]-introᵣ p)

    R : (a ∈ (l₁ ++ l₂)) → ((a ∈ l₁) ∨ (a ∈ l₂))
    R {l₁ = ∅}      p     = [∨]-introᵣ p
    R {l₁ = x ⊰ l₁} (• p) = [∨]-introₗ (• p)
    R {l₁ = x ⊰ l₁} (⊰ p) with R {l₁ = l₁} p
    ... | [∨]-introₗ q = [∨]-introₗ (⊰ q)
    ... | [∨]-introᵣ q = [∨]-introᵣ q

  [∈]-postpend : (a ∈ postpend a l)
  [∈]-postpend{l = ∅}     = use (reflexivity(_≡ₛ_))
  [∈]-postpend{l = _ ⊰ l} = skip([∈]-postpend{l = l})

module _ ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
  private variable f : A → B
  private variable l l₁ l₂ : List(T)
  private variable a b c x : T

  [∈]-map : ⦃ func-f : Function(f) ⦄ → (a ∈ l) → (f(a) ∈ (map f(l)))
  [∈]-map {f = f} (use p)  = use (congruence₁(f) p)
  [∈]-map         (skip p) = skip([∈]-map p)

{- TODO: Stuff below is supposed to be moved to Structure.Sets.Proofs

[∈][++]-expandₗ : (a ∈ l₂) → (a ∈ (l₁ ++ l₂))
[∈][++]-expandₗ {l₂ = l₂}{l₁ = l₁} = [↔]-to-[←] ([∈][++] {l₁ = l₁}{l₂ = l₂}) ∘ [∨]-introᵣ

[∈][++]-expandᵣ : (a ∈ l₁) → (a ∈ (l₁ ++ l₂))
[∈][++]-expandᵣ {l₁ = l₁}{l₂ = l₂} = [↔]-to-[←] ([∈][++] {l₁ = l₁}{l₂ = l₂}) ∘ [∨]-introₗ

[∈][⊰]-reorderₗ : (a ∈ (l₁ ++ (x ⊰ l₂))) → (a ∈ (x ⊰ (l₁ ++ l₂)))
[∈][⊰]-reorderₗ (a∈l₁++xl₂) = [∨]-elim left right ([↔]-to-[→] [∈]-[++] (a∈l₁++xl₂)) where
  left : (a ∈ l₁) → (a ∈ (x ⊰ (l₁ ++ l₂)))
  left (a∈l₁) = [∈][⊰]-expand ([∈][++]-expandᵣ {a}{l₁}{l₂} (a∈l₁))

  right : ∀{a} → (a ∈ (x ⊰ l₂)) → (a ∈ (x ⊰ (l₁ ++ l₂)))
  {-right ([∈]-id)              = use
  right ([∈][⊰]-expand (a∈l₂)) = [∈][⊰]-expand ([∈][++]-expandₗ {_}{l₁}{l₂} (a∈l₂))-}

-- [∈][⊰]-reorderᵣ : ∀{a x}{l₁ l₂} → (a ∈ (x ⊰ (l₁ ++ l₂))) → (a ∈ (l₁ ++ (x ⊰ l₂)))
-- [∈][⊰]-reorderᵣ {a}{x}{l₁}{l₂} ([∈]-id) = 
-- [∈][⊰]-reorderᵣ {a}{x}{l₁}{l₂} ([∈][⊰]-expand (a∈l₁++l₂)) = 

[∈]-in-middle : (a ∈ (l₁ ++ singleton(a) ++ l₂))
[∈]-in-middle{a}{l₁}{l₂} = [↔]-to-[←] ([∈]-[++] {a}{l₁ ++ singleton(a)}{l₂}) ([∨]-introₗ ([∈]-at-last{l = l₁}))

module _ where
  private variable ℓ₂ : Lvl.Level

  [⊆]-substitution : ∀{l₁ l₂ : List(T)} → (l₁ ⊆ l₂) → ∀{P : T → Stmt{ℓ₂}} → (∀{a} → (a ∈ l₂) → P(a)) → (∀{a} → (a ∈ l₁) → P(a))
  [⊆]-substitution (l₁⊆l₂) proof = proof ∘ (l₁⊆l₂)

  [⊇]-substitution : ∀{l₁ l₂ : List(T)} → (l₁ ⊇ l₂) → ∀{P : T → Stmt{ℓ₂}} → (∀{a} → (a ∈ l₁) → P(a)) → (∀{a} → (a ∈ l₂) → P(a))
  [⊇]-substitution (l₁⊇l₂) proof = proof ∘ (l₁⊇l₂)

  [≡]-substitutionₗ : ∀{l₁ l₂ : List(T)} → (l₁ ≡ l₂) → ∀{P : T → Stmt{ℓ₂}} → (∀{a} → (a ∈ l₁) → P(a)) → (∀{a} → (a ∈ l₂) → P(a))
  [≡]-substitutionₗ (l₁≡l₂) = [⊆]-substitution ([↔]-to-[←] (l₁≡l₂))

  [≡]-substitutionᵣ : ∀{l₁ l₂ : List(T)} → (l₁ ≡ l₂) → ∀{P : T → Stmt{ℓ₂}} → (∀{a} → (a ∈ l₂) → P(a)) → (∀{a} → (a ∈ l₁) → P(a))
  [≡]-substitutionᵣ (l₁≡l₂) = [⊆]-substitution ([↔]-to-[→] (l₁≡l₂))
-}

{-
open import Structure.Relator.Properties

instance
  [⊆]-reflexivity : Reflexivity(_⊆_)
  Reflexivity.proof [⊆]-reflexivity = id

instance
  [⊆]-antisymmetry : Antisymmetry(_⊆_)(_≡_)
  Antisymmetry.proof [⊆]-antisymmetry = swap [↔]-intro

instance
  [⊆]-transitivity : Transitivity(_⊆_)
  Transitivity.proof [⊆]-transitivity xy yz = yz ∘ xy

instance
  [⊆]-reflexivity : Reflexivity(_⊆_)

[≡]-reflexivity : ∀{L} → (L ≡ L)
-- [≡]-reflexivity = [↔]-intro [⊆]-reflexivity [⊆]-reflexivity


[≡]-symmetry : ∀{l₁ l₂} → (l₁ ≡ l₂) → (l₂ ≡ l₁)
[≡]-symmetry (l₁≡l₂) {x} with (l₁≡l₂){x}
... | [↔]-intro l r = [↔]-intro r l


[≡]-transitivity : ∀{l₁ l₂ L₃} → (l₁ ≡ l₂) → (l₂ ≡ L₃) → (l₁ ≡ L₃)
[≡]-transitivity (l₁≡l₂) (l₂≡L₃) {x} with [∧]-intro ((l₁≡l₂){x}) ((l₂≡L₃){x})
... | ([∧]-intro (lr₁) (lr₂)) = [↔]-transitivity  (lr₁) (lr₂)

-- [⊆]-application : ∀{l₁ l₂} → (l₁ ⊆ l₂) → ∀{f} → (map f(l₁))⊆(map f(l₂))
-- [⊆]-application proof fl₁ = [∈]-proof.application ∘ proof
-- (∀{x} → (x ∈ l₂) → (x ∈ l₁)) → ∀{f} → (∀{x} → (x ∈ map f(l₂)) → (x ∈ map f(l₁)))

{-
[≡]-included-in : ∀{L : List(T)}{x} → (x ∈ L) → ((x ⊰ L) ≡ L)
[≡]-included-in xL = [⊆]-antisymmetry (sub xL) (super xL) where
  super : ∀{L : List(T)}{x} → (x ∈ L) → ((x ⊰ L) ⊇ L)
  super [∈]-id  [∈]-id  = [∈]-id
  super [∈]-id  (skip p) = skip ?
  super (skip p) [∈]-id  = skip(use ?)
  super (skip p ) (skip q) = skip(skip ?)

  sub : ∀{L : List(T)}{x} → (x ∈ L) → ((x ⊰ L) ⊆ L)
  sub use  use          = use
  sub use  (skip ⦃ p ⦄) = p
  sub skip use          = skip
  sub skip (skip ⦃ p ⦄) = p
-}

postulate [≡]-included-subset : ∀{l₁ l₂ : List(T)} → (l₁ ⊆ l₂) → ((l₁ ++ l₂) ≡ l₂)

postulate [≡]-subset-[++] : ∀{L l₁ l₂ : List(T)} → (l₁ ⊆ L) → (l₂ ⊆ L) → (l₁ ++ l₂ ⊆ L)


[⊆]-with-[⊰] : ∀{l₁ l₂ : List(T)} → (l₁ ⊆ l₂) → ∀{b} → (l₁ ⊆ (b ⊰ l₂))
[⊆]-with-[⊰] (l₁⊆l₂) (x∈l₁) = [∈][⊰]-expand ((l₁⊆l₂) (x∈l₁))


[⊆]-with-[++]ₗ : ∀{l₁ l₂ : List(T)} → (l₁ ⊆ l₂) → ∀{L₃} → (l₁ ⊆ (L₃ ++ l₂))
-- [⊆]-with-[++]ₗ {l₁}{l₂} (l₁⊆l₂) {L₃} (x∈l₁) = [∈][++]-expandₗ {_}{L₃}{l₂} ((l₁⊆l₂) (x∈l₁))


[⊆]-with-[++]ᵣ : ∀{l₁ l₂ : List(T)} → (l₁ ⊆ l₂) → ∀{L₃} → (l₁ ⊆ (l₂ ++ L₃))
[⊆]-with-[++]ᵣ {l₁}{l₂} (l₁⊆l₂) {L₃} (x∈l₁) = [∈][++]-expandᵣ {_}{l₂}{L₃} ((l₁⊆l₂) (x∈l₁))

-- TODO: Does this work? It would be easier to "port" all (∈)-theorems to (⊆)-theorems then.
-- [∈]-to-[⊆]-property : ∀{l₂}{f : List(T) → List(T)} → (∀{a} → (a ∈ l₂) → (a ∈ f(l₂))) → (∀{l₁} → (l₁ ⊆ l₂) → (l₁ ⊆ f(l₂)))

-}
