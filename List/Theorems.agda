module List.Theorems {ℓ₁} {ℓ₂} where

import Level as Lvl
open import Functional
open import List
open import List.Properties
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Relator.Equals{ℓ₁} renaming (_≡_ to _[≡]_ ; _≢_ to _[≢]_) hiding ([≡]-substitution)
open import Type{ℓ₂}

-- Statement of whether a list is contained in the beginning of another list
module OrderedContainment {T} where
  data _contains-in-order_ : List{ℓ₂}(T) → List{ℓ₂}(T) → Stmt where
    empty : (∅ contains-in-order ∅)
    use   : ∀{x}{L₁ L₂} → (L₁ contains-in-order L₂) → ((x ⊰ L₁) contains-in-order (x ⊰ L₂))
    skip  : ∀{x}{L₁ L₂} → (L₁ contains-in-order L₂) → ((x ⊰ L₁) contains-in-order L₂)

  self : ∀{L} → (L contains-in-order L)
  self {∅}     = empty
  self {a ⊰ L} = use(self{L})

  emptyᵣ : ∀{L} → (L contains-in-order ∅)
  emptyᵣ {∅}     = empty
  emptyᵣ {a ⊰ L} = skip(emptyᵣ{L})

  [∈]-of-[++]ₗ : ∀{L₁ L₂} → ((L₁ ++ L₂) contains-in-order L₂)
  [∈]-of-[++]ₗ {∅}{∅} = empty
  [∈]-of-[++]ₗ {∅}{L₂} = self
  -- [∈]-of-[++]ₗ {L₁}{∅} = emptyᵣ -- Either this line or the first seems to be redundant
  [∈]-of-[++]ₗ {a₁ ⊰ L₁}{L₂} = skip{a₁}([∈]-of-[++]ₗ{L₁}{L₂})

  constructₗ : ∀{L₁ L₂} → (L₁ contains-in-order L₂) → List{ℓ₂}(T)
  constructₗ {L₁}{_} (_) = L₁

  constructᵣ : ∀{L₁ L₂} → (L₁ contains-in-order L₂) → List{ℓ₂}(T)
  constructᵣ {_}{L₂} (_) = L₂
open OrderedContainment using (_contains-in-order_) public

-- List as finite sets
module Sets {T} where
  open import Numeral.Natural

  -- The statement of whether an element is in a list
  data _∈_ : T → List{ℓ₂}(T) → Stmt where
    [∈]-use  : ∀{a}{L} → (a ∈ (a ⊰ L)) -- Proof of containment when the element is the first element in the list
    [∈]-skip : ∀{a x}{L} → (a ∈ L) → (a ∈ (x ⊰ L)) -- Proof of containment of a longer list when already having a proof of a shorter list

  _∉_ : T → List{ℓ₂}(T) → Stmt
  _∉_ x L = ¬(x ∈ L)

  _∋_ : List{ℓ₂}(T) → T → Stmt
  _∋_ L x = (x ∈ L)

  _∌_ : List{ℓ₂}(T) → T → Stmt
  _∌_ L x = ¬(L ∋ x)

  -- General proofs about the containment relation
  module [∈]-proof where
    open import Logic.Theorems{ℓ₁ Lvl.⊔ ℓ₂}
    open import Numeral.Natural.Oper.Properties

    pattern [∈]-head     {a}{L}          = [∈]-use  {a}{L}
    pattern [∈]-with-[⊰] {a}{x}{L} proof = [∈]-skip {a}{x}{L} (proof)

    [∉]-empty : ∀{a} → (a ∉ ∅)
    [∉]-empty ()

    [∈]-singleton : ∀{a} → (a ∈ ([ a ]))
    [∈]-singleton = [∈]-head

    [∈]-singleton-[≡] : ∀{a b} → (a ∈ ([ b ])) → (a [≡] b)
    [∈]-singleton-[≡] ([∈]-head)  = [≡]-intro
    [∈]-singleton-[≡] ([∈]-with-[⊰] ())

    [∉]-singleton-[≢] : ∀{a b} → (a [≢] b) → (a ∉ ([ b ]))
    [∉]-singleton-[≢] = contrapositive₁ [∈]-singleton-[≡]

    [∈]-of-[++]ᵣ : ∀{a}{L₁ L₂} → (a ∈ (L₁ ++ L₂)) → ((a ∈ L₁)∨(a ∈ L₂))
    [∈]-of-[++]ᵣ {a}{_}{∅} a∈L₁ = [∨]-introₗ([≡]-elimᵣ [++]-identityᵣ {expr ↦ (a ∈ expr)} (a∈L₁))
    [∈]-of-[++]ᵣ {_}{∅}{_} a∈L₂ = [∨]-introᵣ(a∈L₂)
    [∈]-of-[++]ᵣ {_}{_ ⊰ L₁}{L₂} ([∈]-head) = [∨]-introₗ([∈]-head)
    [∈]-of-[++]ᵣ {a}{x ⊰ L₁}{L₂} ([∈]-with-[⊰] a∈L₁) with [∈]-of-[++]ᵣ {a}{L₁}{L₂} (a∈L₁)
    ...                                               | [∨]-introₗ(a∈L₁∖a) = [∨]-introₗ([∈]-with-[⊰](a∈L₁∖a))
    ...                                               | [∨]-introᵣ(a∈L₂) = [∨]-introᵣ(a∈L₂)

    [∈]-of-[++]ₗ : ∀{a}{L₁ L₂} → (a ∈ (L₁ ++ L₂)) ← ((a ∈ L₁)∨(a ∈ L₂))
    [∈]-of-[++]ₗ {_}{∅}{_} ([∨]-introₗ ())
    -- [∈]-of-[++]ₗ {_}{_}{∅} ([∨]-introᵣ ())
    -- [∈]-of-[++]ₗ {a}{_}{∅} ([∨]-introₗ a∈L₁) = [≡]-elimₗ [++]-identityᵣ {expr ↦ (a ∈ expr)} (a∈L₁)
    [∈]-of-[++]ₗ {_}{∅}{_} ([∨]-introᵣ(a∈L₂)) = (a∈L₂)
    [∈]-of-[++]ₗ {_}{_ ⊰ L₁}{L₂} ([∨]-introₗ([∈]-head)) = [∈]-head
    [∈]-of-[++]ₗ {a}{x ⊰ L₁}{L₂} ([∨]-introₗ([∈]-with-[⊰] a∈L₁)) = [∈]-with-[⊰]([∈]-of-[++]ₗ {a}{L₁}{L₂} ([∨]-introₗ(a∈L₁)))
    [∈]-of-[++]ₗ {a}{x ⊰ L₁}{L₂} ([∨]-introᵣ(a∈L₂)) = [∈]-with-[⊰]{a}{x}([∈]-of-[++]ₗ {a}{L₁}{L₂} ([∨]-introᵣ(a∈L₂)))

    [∈]-of-[++] : ∀{a}{L₁ L₂} → (a ∈ (L₁ ++ L₂)) ↔ ((a ∈ L₁)∨(a ∈ L₂))
    [∈]-of-[++] = [↔]-intro [∈]-of-[++]ₗ [∈]-of-[++]ᵣ

    [∈][++]-commutativity : ∀{a}{L₁ L₂} → (a ∈ (L₁ ++ L₂)) → (a ∈ (L₂ ++ L₁))
    [∈][++]-commutativity {a}{L₁}{L₂} a∈L₁++L₂ = [∈]-of-[++]ₗ{a}{L₂}{L₁}([∨]-commutativity([∈]-of-[++]ᵣ(a∈L₁++L₂)))

    construct : ∀{a}{L} → (a ∈ L) → T
    construct{a}(_) = a

    [∈]-apply : ∀{a}{L} → (a ∈ L) → ∀{f} → (f(a) ∈ (map f(L)))
    [∈]-apply ([∈]-head)            = [∈]-head
    [∈]-apply ([∈]-with-[⊰](proof)) = [∈]-with-[⊰]([∈]-apply(proof))

    [∈]-at-last : ∀{L} → ∀{a} → (a ∈ (L ++ singleton(a)))
    [∈]-at-last{∅}        = [∈]-head
    [∈]-at-last{_ ⊰ rest} = [∈]-with-[⊰] ([∈]-at-last{rest})

    [∈]-in-middle : ∀{L₁ L₂} → ∀{a} → (a ∈ (L₁ ++ singleton(a) ++ L₂))
    [∈]-in-middle{L₁} = [∈]-of-[++]ₗ ([∨]-introₗ ([∈]-at-last{L₁}))

  -- Other relators regarding sets
  module Relators where
    open import Functional

    _⊆_ : List{ℓ₂}(T) → List{ℓ₂}(T) → Stmt
    _⊆_ L₁ L₂ = ∀{x} → (x ∈ L₁) → (x ∈ L₂)

    _⊇_ : List{ℓ₂}(T) → List{ℓ₂}(T) → Stmt
    _⊇_ L₁ L₂ = ∀{x} → (x ∈ L₁) ← (x ∈ L₂)

    _≡_ : List{ℓ₂}(T) → List{ℓ₂}(T) → Stmt
    _≡_ L₁ L₂ = ∀{x} → (x ∈ L₁) ↔ (x ∈ L₂)

    _⊈_ : List{ℓ₂}(T) → List{ℓ₂}(T) → Stmt
    _⊈_ L₁ L₂ = ¬(L₁ ⊆ L₂)

    _⊉_ : List{ℓ₂}(T) → List{ℓ₂}(T) → Stmt
    _⊉_ L₁ L₂ = ¬(L₁ ⊇ L₂)

    _≢_ : List{ℓ₂}(T) → List{ℓ₂}(T) → Stmt
    _≢_ L₁ L₂ = ¬(L₁ ≡ L₂)

    [⊆]-substitution : ∀{L₁ L₂ : List{ℓ₂}(T)} → (L₁ ⊆ L₂) → ∀{P : T → Stmt} → (∀{a} → (a ∈ L₂) → P(a)) → (∀{a} → (a ∈ L₁) → P(a))
    [⊆]-substitution (L₁⊆L₂) proof = proof ∘ (L₁⊆L₂)

    [≡]-substitutionₗ : ∀{L₁ L₂ : List{ℓ₂}(T)} → (L₁ ≡ L₂) → ∀{P : T → Stmt} → (∀{a} → (a ∈ L₁) → P(a)) → (∀{a} → (a ∈ L₂) → P(a))
    [≡]-substitutionₗ (L₁≡L₂) = [⊆]-substitution ([↔]-elimₗ (L₁≡L₂))

    [≡]-substitutionᵣ : ∀{L₁ L₂ : List{ℓ₂}(T)} → (L₁ ≡ L₂) → ∀{P : T → Stmt} → (∀{a} → (a ∈ L₂) → P(a)) → (∀{a} → (a ∈ L₁) → P(a))
    [≡]-substitutionᵣ (L₁≡L₂) = [⊆]-substitution ([↔]-elimᵣ (L₁≡L₂))

    -- [⊆]-application : ∀{L₁ L₂} → (L₁ ⊆ L₂) → ∀{f} → (map f(L₁))⊆(map f(L₂))
    -- [⊆]-application proof fL₁ = [∈]-proof.application ∘ proof
    -- (∀{x} → (x ∈ L₂) → (x ∈ L₁)) → ∀{f} → (∀{x} → (x ∈ map f(L₂)) → (x ∈ map f(L₁)))
