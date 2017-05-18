module List.Theorems {l₁} {l₂} where

import Level as Lvl
open import Functional
open import List
open import List.Properties
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Logic.Predicate{l₁}{l₂}
open import Relator.Equals{l₁}{l₂} renaming (_≡_ to _[≡]_ ; _≢_ to _[≢]_)
open import Type{l₁}

-- Statement of whether a list is contained in the beginning of another list
module OrderedContainment {T} where
  data _contains-in-order_ : List{l₁}(T) → List{l₁}(T) → Stmt where
    empty : (∅ contains-in-order ∅)
    use   : ∀{x}{L₁ L₂} → (L₁ contains-in-order L₂) → ((x ⊰ L₁) contains-in-order (x ⊰ L₂))
    skip  : ∀{x}{L₁ L₂} → (L₁ contains-in-order L₂) → ((x ⊰ L₁) contains-in-order L₂)

  self : ∀{L} → (L contains-in-order L)
  self {∅}     = empty
  self {a ⊰ L} = use(self{L})

  emptyᵣ : ∀{L} → (L contains-in-order ∅)
  emptyᵣ {∅}     = empty
  emptyᵣ {a ⊰ L} = skip(emptyᵣ{L})

  concatᵣ : ∀{L₁ L₂} → ((L₁ ++ L₂) contains-in-order L₂)
  concatᵣ {∅}{∅} = empty
  concatᵣ {∅}{L₂} = self
  -- concatᵣ {L₁}{∅} = emptyᵣ -- Either this line or the first seems to be redundant
  concatᵣ {a₁ ⊰ L₁}{L₂} = skip{a₁}(concatᵣ{L₁}{L₂})

  constructₗ : ∀{L₁ L₂} → (L₁ contains-in-order L₂) → List{l₁}(T)
  constructₗ {L₁}{_} (_) = L₁

  constructᵣ : ∀{L₁ L₂} → (L₁ contains-in-order L₂) → List{l₁}(T)
  constructᵣ {_}{L₂} (_) = L₂
open OrderedContainment using (_contains-in-order_) public

-- List as sets
module Sets {T} where
  open import Numeral.Natural

  -- The statement of whether an element is in a list
  data _∈_ : T → List{l₁}(T) → Stmt where
    [∈]-use  : ∀{a}{L} → (a ∈ (a ⊰ L)) -- Proof of containment when the element is the first element in the list
    [∈]-skip : ∀{a x}{L} → (a ∈ L) → (a ∈ (x ⊰ L)) -- Proof of containment of a longer list when already having a proof of a shorter list

  _∉_ : T → List{l₁}(T) → Stmt
  _∉_ x L = ¬(x ∈ L)

  _∋_ : List{l₁}(T) → T → Stmt
  _∋_ L x = (x ∈ L)

  _∌_ : List{l₁}(T) → T → Stmt
  _∌_ L x = ¬(L ∋ x)

  -- General proofs about the containment relation
  module [∈]-proof where
    pattern use  {a}{L}          = [∈]-use  {a}{L}
    pattern skip {a}{x}{L} proof = [∈]-skip {a}{x}{L} (proof)

    empty : ∀{a} → (a ∉ ∅)
    empty ()

    single : ∀{a} → (a ∈ ([ a ]))
    single = use

    concatₗ : ∀{a}{L₁ L₂} → ((a ∈ L₁)∨(a ∈ L₂)) ← (a ∈ (L₁ ++ L₂))
    concatₗ {a}{_}{∅} a∈L₁ = [∨]-introₗ([≡]-elimᵣ [++]-identityᵣ {expr ↦ (a ∈ expr)} (a∈L₁))
    concatₗ {_}{∅}{_} a∈L₂ = [∨]-introᵣ(a∈L₂)
    concatₗ {_}{_ ⊰ L₁}{L₂} (use) = [∨]-introₗ(use)
    concatₗ {a}{x ⊰ L₁}{L₂} (skip a∈L₁) with concatₗ {a}{L₁}{L₂} (a∈L₁)
    ...                                 | [∨]-introₗ(a∈L₁∖a) = [∨]-introₗ(skip(a∈L₁∖a))
    ...                                 | [∨]-introᵣ(a∈L₂) = [∨]-introᵣ(a∈L₂)

    concatᵣ : ∀{a}{L₁ L₂} → ((a ∈ L₁)∨(a ∈ L₂)) → (a ∈ (L₁ ++ L₂))
    concatᵣ {_}{∅}{_} ([∨]-introₗ ())
    -- concatᵣ {_}{_}{∅} ([∨]-introᵣ ())
    -- concatᵣ {a}{_}{∅} ([∨]-introₗ a∈L₁) = [≡]-elimₗ [++]-identityᵣ {expr ↦ (a ∈ expr)} (a∈L₁)
    concatᵣ {_}{∅}{_} ([∨]-introᵣ(a∈L₂)) = (a∈L₂)
    concatᵣ {_}{_ ⊰ L₁}{L₂} ([∨]-introₗ(use)) = use
    concatᵣ {a}{x ⊰ L₁}{L₂} ([∨]-introₗ(skip a∈L₁)) = skip(concatᵣ {a}{L₁}{L₂} ([∨]-introₗ(a∈L₁)))
    concatᵣ {a}{x ⊰ L₁}{L₂} ([∨]-introᵣ(a∈L₂)) = skip{a}{x}(concatᵣ {a}{L₁}{L₂} ([∨]-introᵣ(a∈L₂)))

    concat : ∀{a}{L₁ L₂} → ((a ∈ L₁)∨(a ∈ L₂)) ↔ (a ∈ (L₁ ++ L₂))
    concat = [↔]-intro concatₗ concatᵣ

    -- at : ∀{x}{L} → (n : ℕ) → (x ∈ (reduceᵣ(⊰) L))
    -- at(𝟎)    = use
    -- at(𝐒(n)) = skip(at(n))

  _⊆_ : List{l₁}(T) → List{l₁}(T) → Stmt
  _⊆_ L₁ L₂ = ∀{x} → (x ∈ L₁) ← (x ∈ L₂)

  _⊇_ : List{l₁}(T) → List{l₁}(T) → Stmt
  _⊇_ L₁ L₂ = ∀{x} → (x ∈ L₁) → (x ∈ L₂)

  _≡_ : List{l₁}(T) → List{l₁}(T) → Stmt
  _≡_ L₁ L₂ = ∀{x} → (x ∈ L₁) ↔ (x ∈ L₂)

  _⊈_ : List{l₁}(T) → List{l₁}(T) → Stmt
  _⊈_ L₁ L₂ = ¬(L₁ ⊆ L₂)

  _⊉_ : List{l₁}(T) → List{l₁}(T) → Stmt
  _⊉_ L₁ L₂ = ¬(L₁ ⊇ L₂)

  _≢_ : List{l₁}(T) → List{l₁}(T) → Stmt
  _≢_ L₁ L₂ = ¬(L₁ ≡ L₂)
