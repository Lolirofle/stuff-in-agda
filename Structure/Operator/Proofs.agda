module Structure.Operator.Proofs where

import Lvl
open import Data
open import Data.Tuple
open import Functional hiding (id)
open import Function.Equals
import      Function.Names as Names
open import Logic.IntroInstances
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid
open import Sets.Setoid.Uniqueness
open import Structure.Function.Domain
open import Structure.Function.Multi
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

-- TODO: These are to make the generalized variables work when they depend on each other. Are there any better ways?
private
  module _ {ℓ} {T : Type{ℓ}} ⦃ equiv : Equiv(T) ⦄ where
    select-invol : ∀(f : T → T) → Involution(f) → Type{Lvl.𝟎}
    select-invol _ _ = Data.Unit

  module _ {ℓ} {T : Type{ℓ}} ⦃ equiv : Equiv(T) ⦄ {_▫_ : T → T → T} where
    select-id : ∀(id) → Identity(_▫_)(id) → Type{Lvl.𝟎}
    select-id _ _ = Data.Unit

    select-idₗ : ∀(id) → Identityₗ(_▫_)(id) → Type{Lvl.𝟎}
    select-idₗ _ _ = Data.Unit

    select-idᵣ : ∀(id) → Identityᵣ(_▫_)(id) → Type{Lvl.𝟎}
    select-idᵣ _ _ = Data.Unit

    select-inv : ∀(id)(ident)(inv) → InverseFunction(_▫_) ⦃ [∃]-intro(id) ⦃ ident ⦄ ⦄ (inv) → Type{Lvl.𝟎}
    select-inv _ _ _ _ = Data.Unit

    select-invₗ : ∀(id)(ident)(inv) → InverseFunctionₗ(_▫_) ⦃ [∃]-intro(id) ⦃ ident ⦄ ⦄ (inv) → Type{Lvl.𝟎}
    select-invₗ _ _ _ _ = Data.Unit

    select-invᵣ : ∀(id)(ident)(inv) → InverseFunctionᵣ(_▫_) ⦃ [∃]-intro(id) ⦃ ident ⦄ ⦄ (inv) → Type{Lvl.𝟎}
    select-invᵣ _ _ _ _ = Data.Unit

    select-invPropₗ : ∀(inv) → InversePropertyₗ(_▫_)(inv) → Type{Lvl.𝟎}
    select-invPropₗ _ _ = Data.Unit

    select-invPropᵣ : ∀(inv) → InversePropertyᵣ(_▫_)(inv) → Type{Lvl.𝟎}
    select-invPropᵣ _ _ = Data.Unit

module One {ℓ} {T : Type{ℓ}} ⦃ equiv : Equiv(T) ⦄ {_▫_ : T → T → T} where
  private variable {id idₗ idᵣ ab abₗ abᵣ} : T
  private variable {inv invₗ invᵣ} : T → T
  private variable ⦃ op ⦄ : BinaryOperator ⦃ equiv ⦄ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫_)
  private variable ⦃ comm ⦄ : Commutativity ⦃ equiv ⦄ (_▫_)
  private variable ⦃ cancₗ ⦄ : Cancellationₗ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫_)
  private variable ⦃ cancᵣ ⦄ : Cancellationᵣ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫_)
  private variable ⦃ assoc ⦄ : Associativity ⦃ equiv ⦄ (_▫_)
  private variable ⦃ ident  ⦄ : Identity ⦃ equiv ⦄ (_▫_)(id)
  private variable ⦃ identₗ ⦄ : Identityₗ ⦃ equiv ⦄ (_▫_)(id)
  private variable ⦃ identᵣ ⦄ : Identityᵣ ⦃ equiv ⦄ (_▫_)(id)
  private variable ⦃ inver  ⦄ : InverseFunction ⦃ equiv ⦄ (_▫_) ⦃ [∃]-intro(id) ⦃ ident ⦄ ⦄ (inv)
  private variable ⦃ inverₗ ⦄ : InverseFunctionₗ ⦃ equiv ⦄ (_▫_) ⦃ [∃]-intro(idₗ) ⦃ identₗ ⦄ ⦄ (invₗ)
  private variable ⦃ inverᵣ ⦄ : InverseFunctionᵣ ⦃ equiv ⦄ (_▫_) ⦃ [∃]-intro(idᵣ) ⦃ identᵣ ⦄ ⦄ (invᵣ)
  private variable ⦃ inverPropₗ ⦄ : InversePropertyₗ ⦃ equiv ⦄ (_▫_) (invₗ)
  private variable ⦃ inverPropᵣ ⦄ : InversePropertyᵣ ⦃ equiv ⦄ (_▫_) (invᵣ)
  private variable ⦃ invol ⦄ : Involution ⦃ equiv ⦄ (inv)

  associate-commute4 : let _ = op , assoc in ∀{a b c d} → Names.Commuting(_▫_)(b)(c) → ((a ▫ b) ▫ (c ▫ d) ≡ (a ▫ c) ▫ (b ▫ d))
  associate-commute4 {a}{b}{c}{d} com =
    (a ▫ b) ▫ (c ▫ d) 🝖-[ symmetry(_≡_) (associativity(_▫_) {a ▫ b} {c} {d}) ]
    ((a ▫ b) ▫ c) ▫ d 🝖-[ [≡]-with2ₗ(_▫_)(d) (associativity(_▫_) {a} {b} {c}) ]
    (a ▫ (b ▫ c)) ▫ d 🝖-[ ([≡]-with2ₗ(_▫_)(d) ∘ [≡]-with2ᵣ(_▫_)(a)) com ]
    (a ▫ (c ▫ b)) ▫ d 🝖-[ associativity(_▫_) {a} {c ▫ b} {d} ]
    a ▫ ((c ▫ b) ▫ d) 🝖-[ [≡]-with2ᵣ(_▫_)(a) (associativity(_▫_) {c} {b} {d}) ]
    a ▫ (c ▫ (b ▫ d)) 🝖-[ symmetry(_≡_) (associativity(_▫_) {a} {c} {b ▫ d}) ]
    (a ▫ c) ▫ (b ▫ d) 🝖-end

  associate4-123-321 : let _ = op , assoc in ∀{a b c d} → (((a ▫ b) ▫ c) ▫ d ≡ a ▫ (b ▫ (c ▫ d)))
  associate4-123-321 {a}{b}{c}{d} = associativity(_▫_) 🝖 associativity(_▫_)

  associate4-123-213 : let _ = op , assoc in ∀{a b c d} → (((a ▫ b) ▫ c) ▫ d ≡ (a ▫ (b ▫ c)) ▫ d)
  associate4-123-213 {a}{b}{c}{d} = [≡]-with2ₗ(_▫_)(_) (associativity(_▫_))

  associate4-321-231 : let _ = op , assoc in ∀{a b c d} → (a ▫ (b ▫ (c ▫ d)) ≡ a ▫ ((b ▫ c) ▫ d))
  associate4-321-231 {a}{b}{c}{d} = [≡]-with2ᵣ(_▫_)(_) (symmetry(_≡_) (associativity(_▫_)))

  commuteᵣ-assocₗ : let _ = op , assoc , comm in ∀{a b c} → (((a ▫ b) ▫ c) ≡ ((a ▫ c) ▫ b))
  commuteᵣ-assocₗ {a}{b}{c} =
    (a ▫ b) ▫ c 🝖-[ associativity(_▫_) ]
    a ▫ (b ▫ c) 🝖-[ [≡]-with2ᵣ(_▫_)(_) (commutativity(_▫_)) ]
    a ▫ (c ▫ b) 🝖-[ associativity(_▫_) ]-sym
    (a ▫ c) ▫ b 🝖-end

  commuteₗ-assocᵣ : let _ = op , assoc , comm in ∀{a b c} → ((a ▫ (b ▫ c)) ≡ (b ▫ (a ▫ c)))
  commuteₗ-assocᵣ {a}{b}{c} =
    a ▫ (b ▫ c) 🝖-[ associativity(_▫_) ]-sym
    (a ▫ b) ▫ c 🝖-[ [≡]-with2ₗ(_▫_)(_) (commutativity(_▫_)) ]
    (b ▫ a) ▫ c 🝖-[ associativity(_▫_) ]
    b ▫ (a ▫ c) 🝖-end

  -- When an identity element exists and is the same for both sides, it is unique.
  unique-identity : Unique(Identity(_▫_))
  unique-identity{x₁}{x₂} (intro ⦃ intro identityₗ₁ ⦄ ⦃ intro identityᵣ₁ ⦄) (intro ⦃ intro identityₗ₂ ⦄ ⦃ intro identityᵣ₂ ⦄) =
    x₁      🝖-[ symmetry(_≡_) (identityₗ₂{x₁}) ]
    x₂ ▫ x₁ 🝖-[ identityᵣ₁{x₂} ]
    x₂      🝖-end

  -- An existing left identity is unique when the operator is commutative
  unique-identityₗ-by-commutativity : let _ = comm in Unique(Identityₗ(_▫_))
  unique-identityₗ-by-commutativity {x₁}{x₂} (intro identity₁) (intro identity₂) =
    x₁      🝖-[ symmetry(_≡_) (identity₂{x₁}) ]
    x₂ ▫ x₁ 🝖-[ commutativity(_▫_) {x₂}{x₁} ]
    x₁ ▫ x₂ 🝖-[ identity₁{x₂} ]
    x₂      🝖-end

  -- An existing right identity is unique when the operator is commutative
  unique-identityᵣ-by-commutativity : let _ = comm in Unique(Identityᵣ(_▫_))
  unique-identityᵣ-by-commutativity {x₁}{x₂} (intro identity₁) (intro identity₂) =
    x₁      🝖-[ symmetry(_≡_) (identity₂{x₁}) ]
    x₁ ▫ x₂ 🝖-[ commutativity(_▫_) {x₁}{x₂} ]
    x₂ ▫ x₁ 🝖-[ identity₁{x₂} ]
    x₂      🝖-end

  -- An existing left identity is unique when the operator is cancellable
  unique-identityₗ-by-cancellationᵣ : let _ = cancᵣ in Unique(Identityₗ(_▫_))
  unique-identityₗ-by-cancellationᵣ {x₁}{x₂} (intro identity₁) (intro identity₂) =
    cancellationᵣ(_▫_) {x₁}{x₁}{x₂} (
      x₁ ▫ x₁ 🝖-[ identity₁{x₁} ]
      x₁      🝖-[ symmetry(_≡_) (identity₂{x₁}) ]
      x₂ ▫ x₁ 🝖-end
    ) :of: (x₁ ≡ x₂)

  -- An existing left identity is unique when the operator is cancellable
  unique-identityᵣ-by-cancellationₗ : let _ = cancₗ in Unique(Identityᵣ(_▫_))
  unique-identityᵣ-by-cancellationₗ {x₁}{x₂} (intro identity₁) (intro identity₂) =
    cancellationₗ(_▫_) {x₂}{x₁}{x₂} (
      x₂ ▫ x₁ 🝖-[ identity₁{x₂} ]
      x₂      🝖-[ symmetry(_≡_) (identity₂{x₂}) ]
      x₂ ▫ x₂ 🝖-end
    ) :of: (x₁ ≡ x₂)

  -- When identities for both sides exists, they are the same
  unique-identities : ⦃ _ : Identityₗ(_▫_)(idₗ) ⦄ → ⦃ _ : Identityᵣ(_▫_)(idᵣ) ⦄ → (idₗ ≡ idᵣ)
  unique-identities {idₗ}{idᵣ} =
    idₗ       🝖-[ symmetry(_≡_) (identityᵣ(_▫_)(idᵣ)) ]
    idₗ ▫ idᵣ 🝖-[ identityₗ(_▫_)(idₗ) ]
    idᵣ       🝖-end

  -- When identities for both sides exists, they are the same
  identity-equivalence-by-commutativity : let _ = comm in Identityₗ(_▫_)(id) ↔ Identityᵣ(_▫_)(id)
  identity-equivalence-by-commutativity {id} = [↔]-intro l r where
    l : Identityₗ(_▫_)(id) ← Identityᵣ(_▫_)(id)
    Identityₗ.proof (l identᵣ) {x} = commutativity(_▫_) 🝖 identityᵣ(_▫_)(id) ⦃ identᵣ ⦄

    r : Identityₗ(_▫_)(id) → Identityᵣ(_▫_)(id)
    Identityᵣ.proof (r identₗ) {x} = commutativity(_▫_) 🝖 identityₗ(_▫_)(id) ⦃ identₗ ⦄
    
  -- Cancellation is possible when the operator is associative and have an inverse
  cancellationₗ-by-associativity-inverse : let _ = op , assoc , inverₗ in Cancellationₗ(_▫_)
  Cancellationₗ.proof(cancellationₗ-by-associativity-inverse {idₗ} {invₗ} ) {x}{a}{b} (xa≡xb) =
    a                🝖-[ symmetry(_≡_) (identityₗ(_▫_)(idₗ) {a}) ]
    idₗ ▫ a          🝖-[ [≡]-with2ₗ(_▫_)(a) (symmetry(_≡_) (inverseFunctionₗ(_▫_)(invₗ) {x})) ]
    (invₗ x ▫ x) ▫ a 🝖-[ associativity(_▫_) {invₗ(x)}{x}{a} ]
    invₗ x ▫ (x ▫ a) 🝖-[ [≡]-with2ᵣ(_▫_)(invₗ(x)) (xa≡xb) ]
    invₗ x ▫ (x ▫ b) 🝖-[ symmetry(_≡_) (associativity(_▫_) {invₗ(x)}{x}{b}) ]
    (invₗ x ▫ x) ▫ b 🝖-[ [≡]-with2ₗ(_▫_)(b) (inverseFunctionₗ(_▫_)(invₗ) {x}) ]
    idₗ ▫ b          🝖-[ identityₗ(_▫_)(idₗ){b} ]
    b                🝖-end
    -- TODO: This pattern of applying symmetric transitivity rules, make it a function

  -- Cancellation is possible when the operator is associative and have an inverse
  cancellationᵣ-by-associativity-inverse : let _ = op , assoc , inverᵣ in Cancellationᵣ(_▫_)
  Cancellationᵣ.proof(cancellationᵣ-by-associativity-inverse {idᵣ} {invᵣ} ) {x}{a}{b} (xa≡xb) =
    a                🝖-[ symmetry(_≡_) (identityᵣ(_▫_)(idᵣ)) ]
    a ▫ idᵣ          🝖-[ [≡]-with2ᵣ(_▫_)(_) (symmetry(_≡_) (inverseFunctionᵣ(_▫_)(invᵣ))) ]
    a ▫ (x ▫ invᵣ x) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
    (a ▫ x) ▫ invᵣ x 🝖-[ [≡]-with2ₗ(_▫_)(_) (xa≡xb) ]
    (b ▫ x) ▫ invᵣ x 🝖-[ associativity(_▫_) ]
    b ▫ (x ▫ invᵣ x) 🝖-[ [≡]-with2ᵣ(_▫_)(_) (inverseFunctionᵣ(_▫_)(invᵣ)) ]
    b ▫ idᵣ          🝖-[ identityᵣ(_▫_)(idᵣ) ]
    b                🝖-end

  -- When something and something else's inverse is the identity element, they are equal
  equality-zeroₗ : let _ = op , assoc , select-inv(id)(ident)(inv)(inver) in ∀{x y} → (x ≡ y) ← (x ▫ inv(y) ≡ id)
  equality-zeroₗ {id}{inv} {x}{y} (proof) =
    x                🝖-[ symmetry(_≡_) (identity-right(_▫_)(id)) ]
    x ▫ id           🝖-[ symmetry(_≡_) ([≡]-with2ᵣ(_▫_)(x) (inverseFunction-left(_▫_)(inv))) ]
    x ▫ (inv(y) ▫ y) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
    (x ▫ inv(y)) ▫ y 🝖-[ [≡]-with2ₗ(_▫_)(y) (proof) ]
    id ▫ y           🝖-[ identity-left(_▫_)(id) ]
    y                🝖-end

  equality-zeroᵣ : let _ = op , assoc , select-inv(id)(ident)(inv)(inver) in ∀{x y} → (x ≡ y) → (x ▫ inv(y) ≡ id)
  equality-zeroᵣ {id}{inv} {x}{y} (proof) =
    x ▫ inv(y) 🝖-[ [≡]-with2ₗ(_▫_)(inv(y)) proof ]
    y ▫ inv(y) 🝖-[ inverseFunctionᵣ(_▫_)(inv) ]
    id         🝖-end

  commuting-id : let _ = select-id(id)(ident) in ∀{x} → (id ▫ x ≡ x ▫ id)
  commuting-id {id} {x} =
    id ▫ x 🝖-[ identity-left(_▫_)(id) ]
    x      🝖-[ symmetry(_≡_) (identity-right(_▫_)(id)) ]
    x ▫ id 🝖-end

  squeezed-inverse : let _ = op , select-id(id)(ident) in ∀{a b x y} → (a ▫ b ≡ id) → ((x ▫ (a ▫ b)) ▫ y ≡ x ▫ y)
  squeezed-inverse {id} {a}{b}{x}{y} abid =
    (x ▫ (a ▫ b)) ▫ y 🝖-[ ([≡]-with2ₗ(_▫_)(_) ∘ [≡]-with2ᵣ(_▫_)(_)) abid ]
    (x ▫ id) ▫ y      🝖-[ [≡]-with2ₗ(_▫_)(_) (identity-right(_▫_)(id)) ]
    x ▫ y             🝖-end

  double-inverse : let _ = cancᵣ , select-inv(id)(ident)(inv)(inver) in ∀{x} → (inv(inv x) ≡ x)
  double-inverse {id}{inv} {x} =
    (cancellationᵣ(_▫_)
      ((
        (inverseFunction-left(_▫_)(inv)                    :of: (inv(inv x) ▫ inv(x) ≡ id))
        🝖 (symmetry(_≡_) (inverseFunction-right(_▫_)(inv)) :of: (id ≡ x ▫ inv(x)))
      ) :of: (inv(inv x) ▫ inv(x) ≡ x ▫ inv(x)))
    ) :of: (inv(inv x) ≡ x)

  double-inverseₗ-by-id : let _ = op , assoc , select-id(id)(ident) , select-invₗ(id)(Identity.left(ident))(invₗ)(inverₗ) in ∀{x} → (invₗ(invₗ x) ≡ x)
  double-inverseₗ-by-id {id}{inv} {x} =
    inv(inv(x))                🝖-[ symmetry(_≡_) (identityᵣ(_▫_)(id)) ]
    inv(inv(x)) ▫ id           🝖-[ [≡]-with2ᵣ(_▫_)(_) (symmetry(_≡_) (inverseFunctionₗ(_▫_)(inv))) ]
    inv(inv(x)) ▫ (inv(x) ▫ x) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
    (inv(inv(x)) ▫ inv(x)) ▫ x 🝖-[ [≡]-with2ₗ(_▫_)(_) (inverseFunctionₗ(_▫_)(inv)) ]
    id ▫ x                     🝖-[ identityₗ(_▫_)(id) ]
    x                          🝖-end

  double-inverseᵣ-by-id : let _ = op , assoc , select-id(id)(ident) , select-invᵣ(id)(Identity.right(ident))(invᵣ)(inverᵣ) in ∀{x} → (invᵣ(invᵣ x) ≡ x)
  double-inverseᵣ-by-id {id}{inv} {x} =
    inv(inv(x))                🝖-[ symmetry(_≡_) (identityₗ(_▫_)(id)) ]
    id ▫ inv(inv(x))           🝖-[ [≡]-with2ₗ(_▫_)(_) (symmetry(_≡_) (inverseFunctionᵣ(_▫_)(inv))) ]
    (x ▫ inv(x)) ▫ inv(inv(x)) 🝖-[ associativity(_▫_) ]
    x ▫ (inv(x) ▫ inv(inv(x))) 🝖-[ [≡]-with2ᵣ(_▫_)(_) (inverseFunctionᵣ(_▫_)(inv)) ]
    x ▫ id                     🝖-[ identityᵣ(_▫_)(id) ]
    x                          🝖-end

  inverse-equivalence-by-id : let _ = op , assoc , select-id(id)(ident) in InverseFunctionₗ(_▫_)(inv) ↔ InverseFunctionᵣ(_▫_)(inv)
  inverse-equivalence-by-id {id}{inv} = [↔]-intro l r where
    l : InverseFunctionₗ(_▫_)(inv) ← InverseFunctionᵣ(_▫_)(inv)
    InverseFunctionₗ.proof (l inverᵣ) {x} =
      inv(x) ▫ x           🝖-[ [≡]-with2ᵣ(_▫_)(_) (symmetry(_≡_) (double-inverseᵣ-by-id ⦃ inverᵣ = inverᵣ ⦄)) ]
      inv(x) ▫ inv(inv(x)) 🝖-[ inverseFunctionᵣ(_▫_)(inv) ⦃ inverᵣ ⦄ ]
      id                   🝖-end
    r : InverseFunctionₗ(_▫_)(inv) → InverseFunctionᵣ(_▫_)(inv)
    InverseFunctionᵣ.proof (r inverₗ) {x} =
      x ▫ inv(x)           🝖-[ [≡]-with2ₗ(_▫_)(_) (symmetry(_≡_) (double-inverseₗ-by-id ⦃ inverₗ = inverₗ ⦄)) ]
      inv(inv(x)) ▫ inv(x) 🝖-[ inverseFunctionₗ(_▫_)(inv) ⦃ inverₗ ⦄ ]
      id                   🝖-end

  cancellationₗ-by-group : let _ = op , assoc , select-invₗ(idₗ)(identₗ)(invₗ)(inverₗ) in Cancellationₗ(_▫_)
  Cancellationₗ.proof (cancellationₗ-by-group {id}{inv}) {a}{b}{c} abac =
    b                🝖-[ symmetry(_≡_) (identityₗ(_▫_)(id)) ]
    id ▫ b           🝖-[ [≡]-with2ₗ(_▫_)(_) (symmetry(_≡_) (inverseFunctionₗ(_▫_)(inv))) ]
    (inv(a) ▫ a) ▫ b 🝖-[ associativity(_▫_) ]
    inv(a) ▫ (a ▫ b) 🝖-[ [≡]-with2ᵣ(_▫_)(_) abac ]
    inv(a) ▫ (a ▫ c) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
    (inv(a) ▫ a) ▫ c 🝖-[ [≡]-with2ₗ(_▫_)(_) (inverseFunctionₗ(_▫_)(inv)) ]
    id ▫ c           🝖-[ identityₗ(_▫_)(id) ]
    c                🝖-end

  cancellationᵣ-by-group : let _ = op , assoc , select-invᵣ(idᵣ)(identᵣ)(invᵣ)(inverᵣ) in Cancellationᵣ(_▫_)
  Cancellationᵣ.proof (cancellationᵣ-by-group {id}{inv}) {c}{a}{b} acbc =
    a                🝖-[ symmetry(_≡_) (identityᵣ(_▫_)(id)) ]
    a ▫ id           🝖-[ [≡]-with2ᵣ(_▫_)(_) (symmetry(_≡_) (inverseFunctionᵣ(_▫_)(inv))) ]
    a ▫ (c ▫ inv(c)) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
    (a ▫ c) ▫ inv(c) 🝖-[ [≡]-with2ₗ(_▫_)(_) acbc ]
    (b ▫ c) ▫ inv(c) 🝖-[ associativity(_▫_) ]
    b ▫ (c ▫ inv(c)) 🝖-[ [≡]-with2ᵣ(_▫_)(_) (inverseFunctionᵣ(_▫_)(inv)) ]
    b ▫ id           🝖-[ identityᵣ(_▫_)(id) ]
    b                🝖-end

  inverse-distribution : let _ = op , assoc , select-inv(id)(ident)(inv)(inver) in ∀{x y} → (inv(x ▫ y) ≡ inv(y) ▫ inv(x))
  inverse-distribution {id}{inv} {x}{y} =
    (cancellationᵣ(_▫_) ⦃ cancellationᵣ-by-group ⦄
      ((
        inv(x ▫ y) ▫ (x ▫ y)         🝖-[ inverseFunction-left(_▫_)(inv) ]
        id                           🝖-[ symmetry(_≡_) (inverseFunction-left(_▫_)(inv)) ]
        inv(y) ▫ y                   🝖-[ symmetry(_≡_) (squeezed-inverse (inverseFunction-left(_▫_)(inv))) ]
        (inv(y) ▫ (inv(x) ▫ x)) ▫ y  🝖-[ [≡]-with2ₗ(_▫_)(_) (symmetry(_≡_) (associativity(_▫_))) ]
        ((inv(y) ▫ inv(x)) ▫ x) ▫ y  🝖-[ associativity(_▫_) ]
        (inv(y) ▫ inv(x)) ▫ (x ▫ y)  🝖-end
      ) :of: (inv(x ▫ y) ▫ (x ▫ y) ≡ (inv(y) ▫ inv(x)) ▫ (x ▫ y)))
    ) :of: (inv(x ▫ y) ≡ inv(y) ▫ inv(x))

  inverse-distribute-to-inverse : let _ = op , assoc , select-inv(id)(ident)(inv)(inver) in ∀{x y} → inv(inv x ▫ inv y) ≡ y ▫ x
  inverse-distribute-to-inverse {id}{inv} {x}{y} =
    inv(inv x ▫ inv y)      🝖-[ inverse-distribution ]
    inv(inv y) ▫ inv(inv x) 🝖-[ [≡]-with2ᵣ(_▫_)(_) (double-inverse ⦃ cancᵣ = cancellationᵣ-by-group ⦄) ]
    inv(inv y) ▫ x          🝖-[ [≡]-with2ₗ(_▫_)(_) (double-inverse ⦃ cancᵣ = cancellationᵣ-by-group ⦄) ]
    y ▫ x                   🝖-end

  unique-inverseₗ-by-id : let _ = op , assoc , select-id(id)(ident) in Unique(InverseFunctionₗ(_▫_))
  unique-inverseₗ-by-id {id = id} {x = inv₁} {inv₂} inverse₁ inverse₂ = intro \{x} →
    (
      inv₁(x)                             🝖-[ symmetry(_≡_) (identityᵣ(_▫_)(id)) ]
      inv₁(x) ▫ id                        🝖-[ [≡]-with2ᵣ(_▫_)(_) (symmetry(_≡_) (inverseFunctionₗ(_▫_)(inv₂) ⦃ inverse₂ ⦄)) ]
      inv₁(x) ▫ (inv₂(inv₂(x)) ▫ inv₂(x)) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
      (inv₁(x) ▫ inv₂(inv₂(x))) ▫ inv₂(x) 🝖-[ [≡]-with2ₗ(_▫_)(_) ([≡]-with2ᵣ(_▫_)(_) (double-inverseₗ-by-id ⦃ inverₗ = inverse₂ ⦄)) ]
      (inv₁(x) ▫ x) ▫ inv₂(x)             🝖-[ [≡]-with2ₗ(_▫_)(_) (inverseFunctionₗ(_▫_)(inv₁) ⦃ inverse₁ ⦄) ]
      id ▫ inv₂(x)                        🝖-[ identityₗ(_▫_)(id) ]
      inv₂(x)                             🝖-end
    )

  unique-inverseᵣ-by-id : let _ = op , assoc , select-id(id)(ident) in Unique(InverseFunctionᵣ(_▫_))
  unique-inverseᵣ-by-id {id = id} {x = inv₁} {inv₂} inverse₁ inverse₂ = intro \{x} →
    (
      inv₁(x)                             🝖-[ symmetry(_≡_) (identityₗ(_▫_)(id)) ]
      id ▫ inv₁(x)                        🝖-[ [≡]-with2ₗ(_▫_)(_) (symmetry(_≡_) (inverseFunctionᵣ(_▫_)(inv₂) ⦃ inverse₂ ⦄)) ]
      (inv₂(x) ▫ inv₂(inv₂(x))) ▫ inv₁(x) 🝖-[ associativity(_▫_) ]
      inv₂(x) ▫ (inv₂(inv₂(x)) ▫ inv₁(x)) 🝖-[ [≡]-with2ᵣ(_▫_)(_) ([≡]-with2ₗ(_▫_)(_) (double-inverseᵣ-by-id ⦃ inverᵣ = inverse₂ ⦄)) ]
      inv₂(x) ▫ (x ▫ inv₁(x))             🝖-[ [≡]-with2ᵣ(_▫_)(_) (inverseFunctionᵣ(_▫_)(inv₁) ⦃ inverse₁ ⦄) ]
      inv₂(x) ▫ id                        🝖-[ identityᵣ(_▫_)(id) ]
      inv₂(x)                             🝖-end
    )

  unique-inverses : let _ = op , assoc , select-id(id)(ident) in ⦃ _ : InverseFunctionₗ(_▫_)(invₗ) ⦄ → ⦃ _ : InverseFunctionᵣ(_▫_)(invᵣ) ⦄ → (invₗ ≡ invᵣ)
  unique-inverses {id} {invₗ} {invᵣ} = intro \{x} →
    (
      invₗ(x)                 🝖-[ symmetry(_≡_) (identityᵣ(_▫_)(id)) ]
      invₗ(x) ▫ id            🝖-[ [≡]-with2ᵣ(_▫_)(_) (symmetry(_≡_) (inverseFunctionᵣ(_▫_)(invᵣ))) ]
      invₗ(x) ▫ (x ▫ invᵣ(x)) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
      (invₗ(x) ▫ x) ▫ invᵣ(x) 🝖-[ [≡]-with2ₗ(_▫_)(_) (inverseFunctionₗ(_▫_)(invₗ)) ]
      id ▫ invᵣ(x)            🝖-[ identityₗ(_▫_)(id) ]
      invᵣ(x)                 🝖-end
    )

  absorber-equivalence-by-commutativity : let _ = comm in Absorberₗ(_▫_)(ab) ↔ Absorberᵣ(_▫_)(ab)
  absorber-equivalence-by-commutativity {ab} = [↔]-intro l r where
    r : Absorberₗ(_▫_)(ab) → Absorberᵣ(_▫_)(ab)
    Absorberᵣ.proof (r absoₗ) {x} =
      x ▫ ab 🝖-[ commutativity(_▫_) ]
      ab ▫ x 🝖-[ absorberₗ(_▫_)(ab) ⦃ absoₗ ⦄ ]
      ab     🝖-end

    l : Absorberₗ(_▫_)(ab) ← Absorberᵣ(_▫_)(ab)
    Absorberₗ.proof (l absoᵣ) {x} =
      ab ▫ x 🝖-[ commutativity(_▫_) ]
      x ▫ ab 🝖-[ absorberᵣ(_▫_)(ab) ⦃ absoᵣ ⦄ ]
      ab     🝖-end

  inverse-propertyₗ-by-groupₗ : let _ = op , assoc , select-invₗ(id)(identₗ)(inv)(inverₗ) in InversePropertyₗ(_▫_)(inv)
  InversePropertyₗ.proof (inverse-propertyₗ-by-groupₗ {id = id}{inv = inv}) {x} {y} =
    inv(x) ▫ (x ▫ y) 🝖-[ associativity(_▫_) ]-sym
    (inv(x) ▫ x) ▫ y 🝖-[ [≡]-with2ₗ(_▫_)(y) (inverseFunctionₗ(_▫_)(inv)) ]
    id ▫ y           🝖-[ identityₗ(_▫_)(id) ]
    y                🝖-end

  inverse-propertyᵣ-by-groupᵣ : let _ = op , assoc , select-invᵣ(id)(identᵣ)(inv)(inverᵣ) in InversePropertyᵣ(_▫_)(inv)
  InversePropertyᵣ.proof (inverse-propertyᵣ-by-groupᵣ {id = id}{inv = inv}) {x} {y} =
    (x ▫ y) ▫ inv(y) 🝖-[ associativity(_▫_) ]
    x ▫ (y ▫ inv(y)) 🝖-[ [≡]-with2ᵣ(_▫_)(x) (inverseFunctionᵣ(_▫_)(inv)) ]
    x ▫ id           🝖-[ identityᵣ(_▫_)(id) ]
    x                🝖-end

  standard-inverse-operatorₗ-by-involuting-inverse-propₗ : let _ = op , select-invol(inv)(invol) , select-invPropₗ(inv)(inverPropₗ) in InverseOperatorₗ(_▫_)(x ↦ y ↦ inv(x) ▫ y)
  InverseOperatorₗ.proof (standard-inverse-operatorₗ-by-involuting-inverse-propₗ {inv = inv}) {x} {y} =
    x ▫ (inv x ▫ y)            🝖-[ [≡]-with2ₗ(_▫_)((inv x ▫ y)) (involution(inv)) ]-sym
    inv(inv(x)) ▫ (inv x ▫ y)  🝖-[ inversePropₗ(_▫_)(inv) ]
    y                          🝖-end

  standard-inverse-inverse-operatorₗ-by-inverse-propₗ : let _ = select-invPropₗ(inv)(inverPropₗ) in InverseOperatorₗ(x ↦ y ↦ inv(x) ▫ y)(_▫_)
  InverseOperatorₗ.proof (standard-inverse-inverse-operatorₗ-by-inverse-propₗ {inv = inv}) {x} {y} = inversePropₗ(_▫_)(inv)

  standard-inverse-operatorᵣ-by-involuting-inverse-propᵣ : let _ = op , select-invol(inv)(invol) , select-invPropᵣ(inv)(inverPropᵣ) in InverseOperatorᵣ(_▫_)(x ↦ y ↦ x ▫ inv(y))
  InverseOperatorᵣ.proof (standard-inverse-operatorᵣ-by-involuting-inverse-propᵣ {inv = inv}) {x} {y} =
    (x ▫ inv y) ▫ y           🝖-[ [≡]-with2ᵣ(_▫_)((x ▫ inv y)) (involution(inv)) ]-sym
    (x ▫ inv y) ▫ inv(inv(y)) 🝖-[ inversePropᵣ(_▫_)(inv) ]
    x                         🝖-end

  standard-inverse-inverse-operatorᵣ-by-inverse-propᵣ : let _ = select-invPropᵣ(inv)(inverPropᵣ) in InverseOperatorᵣ(x ↦ y ↦ x ▫ inv(y))(_▫_)
  InverseOperatorᵣ.proof (standard-inverse-inverse-operatorᵣ-by-inverse-propᵣ {inv = inv}) {x} {y} = inversePropᵣ(_▫_)(inv)

  inverseᵣ-by-assoc-inv-propᵣ : let _ = op , assoc , select-idₗ(id)(identₗ) , select-invPropᵣ(inv)(inverPropᵣ) in InverseFunctionᵣ(_▫_) ⦃ [∃]-intro(id) ⦃ identᵣ ⦄ ⦄ (inv)
  InverseFunctionᵣ.proof (inverseᵣ-by-assoc-inv-propᵣ {id = id} {inv = inv}) {x} =
    x ▫ inv x        🝖-[ identityₗ(_▫_)(id) ]-sym
    id ▫ (x ▫ inv x) 🝖-[ associativity(_▫_) ]-sym
    (id ▫ x) ▫ inv x 🝖-[ inversePropᵣ(_▫_)(inv) ]
    id               🝖-end

module OneTypeTwoOp {ℓ} {T : Type{ℓ}} ⦃ equiv : Equiv(T) ⦄ {_▫₁_ _▫₂_ : T → T → T} where
  private variable {id} : T
  private variable {inv} : T → T

  private variable ⦃ op₁ ⦄ : BinaryOperator ⦃ equiv ⦄ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₁_)
  private variable ⦃ comm₁ ⦄ : Commutativity ⦃ equiv ⦄ (_▫₁_)
  private variable ⦃ cancₗ₁ ⦄ : Cancellationₗ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₁_)
  private variable ⦃ cancᵣ₁ ⦄ : Cancellationᵣ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₁_)
  private variable ⦃ assoc₁ ⦄ : Associativity ⦃ equiv ⦄ (_▫₁_)
  private variable ⦃ ident₁  ⦄ : Identity ⦃ equiv ⦄ (_▫₁_)(id)
  private variable ⦃ identₗ₁ ⦄ : Identityₗ ⦃ equiv ⦄ (_▫₁_)(id)
  private variable ⦃ identᵣ₁ ⦄ : Identityᵣ ⦃ equiv ⦄ (_▫₁_)(id)
  private variable ⦃ inver₁  ⦄ : InverseFunction ⦃ equiv ⦄ (_▫₁_) ⦃ [∃]-intro(id) ⦃ ident₁ ⦄ ⦄ (inv)
  private variable ⦃ inverₗ₁ ⦄ : InverseFunctionₗ ⦃ equiv ⦄ (_▫₁_) ⦃ [∃]-intro(id) ⦃ identₗ₁ ⦄ ⦄ (inv)
  private variable ⦃ inverᵣ₁ ⦄ : InverseFunctionᵣ ⦃ equiv ⦄ (_▫₁_) ⦃ [∃]-intro(id) ⦃ identᵣ₁ ⦄ ⦄ (inv)

  private variable ⦃ op₂ ⦄ : BinaryOperator ⦃ equiv ⦄ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₂_)
  private variable ⦃ comm₂ ⦄ : Commutativity ⦃ equiv ⦄ (_▫₂_)
  private variable ⦃ cancₗ₂ ⦄ : Cancellationₗ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₂_)
  private variable ⦃ cancᵣ₂ ⦄ : Cancellationᵣ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₂_)
  private variable ⦃ assoc₂ ⦄ : Associativity ⦃ equiv ⦄ (_▫₂_)
  private variable ⦃ ident₂  ⦄ : Identity ⦃ equiv ⦄ (_▫₂_)(id)
  private variable ⦃ identₗ₂ ⦄ : Identityₗ ⦃ equiv ⦄ (_▫₂_)(id)
  private variable ⦃ identᵣ₂ ⦄ : Identityᵣ ⦃ equiv ⦄ (_▫₂_)(id)
  private variable ⦃ inver₂  ⦄ : InverseFunction ⦃ equiv ⦄ (_▫₂_) ⦃ [∃]-intro(id) ⦃ ident₂ ⦄ ⦄ (inv)
  private variable ⦃ inverₗ₂ ⦄ : InverseFunctionₗ ⦃ equiv ⦄ (_▫₂_) ⦃ [∃]-intro(id) ⦃ identₗ₂ ⦄ ⦄ (inv)
  private variable ⦃ inverᵣ₂ ⦄ : InverseFunctionᵣ ⦃ equiv ⦄ (_▫₂_) ⦃ [∃]-intro(id) ⦃ identᵣ₂ ⦄ ⦄ (inv)

  private variable ⦃ distriₗ ⦄ : Distributivityₗ ⦃ equiv ⦄ (_▫₁_)(_▫₂_)
  private variable ⦃ distriᵣ ⦄ : Distributivityᵣ ⦃ equiv ⦄ (_▫₁_)(_▫₂_)
  private variable ⦃ absorpₗ ⦄ : Absorptionₗ ⦃ equiv ⦄ (_▫₁_)(_▫₂_)
  private variable ⦃ absorpᵣ ⦄ : Absorptionᵣ ⦃ equiv ⦄ (_▫₁_)(_▫₂_)

  distributivity-equivalence-by-commutativity : let _ = op₂ , comm₁ in Distributivityₗ(_▫₁_)(_▫₂_) ↔ Distributivityᵣ(_▫₁_)(_▫₂_)
  distributivity-equivalence-by-commutativity = [↔]-intro l r where
    l : Distributivityₗ(_▫₁_)(_▫₂_) ← Distributivityᵣ(_▫₁_)(_▫₂_)
    Distributivityₗ.proof (l distriᵣ) =
      commutativity(_▫₁_)
      🝖 distributivityᵣ(_▫₁_)(_▫₂_) ⦃ distriᵣ ⦄
      🝖 ([≡]-with2ₗ(_▫₂_)(_) (commutativity(_▫₁_)))
      🝖 ([≡]-with2ᵣ(_▫₂_)(_) (commutativity(_▫₁_)))

    r : Distributivityₗ(_▫₁_)(_▫₂_) → Distributivityᵣ(_▫₁_)(_▫₂_)
    Distributivityᵣ.proof (r distriₗ) =
      commutativity(_▫₁_)
      🝖 distributivityₗ(_▫₁_)(_▫₂_) ⦃ distriₗ ⦄
      🝖 ([≡]-with2ₗ(_▫₂_)(_) (commutativity(_▫₁_)))
      🝖 ([≡]-with2ᵣ(_▫₂_)(_) (commutativity(_▫₁_)))

  absorption-equivalence-by-commutativity : let _ = op₁ , comm₁ , comm₂ in Absorptionₗ(_▫₁_)(_▫₂_) ↔ Absorptionᵣ(_▫₁_)(_▫₂_)
  absorption-equivalence-by-commutativity = [↔]-intro l r where
    r : Absorptionₗ(_▫₁_)(_▫₂_) → Absorptionᵣ(_▫₁_)(_▫₂_)
    Absorptionᵣ.proof (r absorpₗ) {x}{y} =
      (x ▫₂ y) ▫₁ y 🝖-[ commutativity(_▫₁_) ]
      y ▫₁ (x ▫₂ y) 🝖-[ [≡]-with2ᵣ(_▫₁_)(_) (commutativity(_▫₂_)) ]
      y ▫₁ (y ▫₂ x) 🝖-[ absorptionₗ(_▫₁_)(_▫₂_) ⦃ absorpₗ ⦄ {y}{x} ]
      y             🝖-end

    l : Absorptionₗ(_▫₁_)(_▫₂_) ← Absorptionᵣ(_▫₁_)(_▫₂_)
    Absorptionₗ.proof (l absorpᵣ) {x}{y} =
      x ▫₁ (x ▫₂ y) 🝖-[ commutativity(_▫₁_) ]
      (x ▫₂ y) ▫₁ x 🝖-[ [≡]-with2ₗ(_▫₁_)(_) (commutativity(_▫₂_)) ]
      (y ▫₂ x) ▫₁ x 🝖-[ absorptionᵣ(_▫₁_)(_▫₂_) ⦃ absorpᵣ ⦄ {y}{x} ]
      x             🝖-end

  absorberₗ-by-absorptionₗ-identityₗ : let _ = absorpₗ , select-idₗ(id)(identₗ₁) in Absorberₗ(_▫₂_)(id)
  Absorberₗ.proof (absorberₗ-by-absorptionₗ-identityₗ {id}) {x} =
    id ▫₂ x         🝖-[ identityₗ(_▫₁_)(id) ]-sym
    id ▫₁ (id ▫₂ x) 🝖-[ absorptionₗ(_▫₁_)(_▫₂_) ]
    id              🝖-end

  absorberᵣ-by-absorptionᵣ-identityᵣ : let _ = absorpᵣ , select-idᵣ(id)(identᵣ₁) in Absorberᵣ(_▫₂_)(id)
  Absorberᵣ.proof (absorberᵣ-by-absorptionᵣ-identityᵣ {id}) {x} =
    x ▫₂ id         🝖-[ identityᵣ(_▫₁_)(id) ]-sym
    (x ▫₂ id) ▫₁ id 🝖-[ absorptionᵣ(_▫₁_)(_▫₂_) ]
    id              🝖-end

module Two {ℓ₁ ℓ₂} {A : Type{ℓ₁}} ⦃ equiv-A : Equiv(A) ⦄ {_▫₁_ : A → A → A} {B : Type{ℓ₂}} ⦃ equiv-B : Equiv(B) ⦄ {_▫₂_ : B → B → B} where
  private variable {id₁} : A
  private variable {inv₁} : A → A
  private variable {id₂} : B
  private variable {inv₂} : B → B

  private variable ⦃ op₁ ⦄ : BinaryOperator ⦃ equiv-A ⦄ ⦃ equiv-A ⦄ ⦃ equiv-A ⦄ (_▫₁_)
  private variable ⦃ comm₁ ⦄ : Commutativity ⦃ equiv-A ⦄ (_▫₁_)
  private variable ⦃ cancₗ₁ ⦄ : Cancellationₗ ⦃ equiv-A ⦄ ⦃ equiv-A ⦄ (_▫₁_)
  private variable ⦃ cancᵣ₁ ⦄ : Cancellationᵣ ⦃ equiv-A ⦄ ⦃ equiv-A ⦄ (_▫₁_)
  private variable ⦃ assoc₁ ⦄ : Associativity ⦃ equiv-A ⦄ (_▫₁_)
  private variable ⦃ ident₁  ⦄ : Identity ⦃ equiv-A ⦄ (_▫₁_)(id₁)
  private variable ⦃ identₗ₁ ⦄ : Identityₗ ⦃ equiv-A ⦄ (_▫₁_)(id₁)
  private variable ⦃ identᵣ₁ ⦄ : Identityᵣ ⦃ equiv-A ⦄ (_▫₁_)(id₁)
  private variable ⦃ inver₁  ⦄ : InverseFunction ⦃ equiv-A ⦄ (_▫₁_) ⦃ [∃]-intro(id₁) ⦃ ident₁ ⦄ ⦄ (inv₁)
  private variable ⦃ inverₗ₁ ⦄ : InverseFunctionₗ ⦃ equiv-A ⦄ (_▫₁_) ⦃ [∃]-intro(id₁) ⦃ identₗ₁ ⦄ ⦄ (inv₁)
  private variable ⦃ inverᵣ₁ ⦄ : InverseFunctionᵣ ⦃ equiv-A ⦄ (_▫₁_) ⦃ [∃]-intro(id₁) ⦃ identᵣ₁ ⦄ ⦄ (inv₁)

  private variable ⦃ op₂ ⦄ : BinaryOperator ⦃ equiv-B ⦄ ⦃ equiv-B ⦄ ⦃ equiv-B ⦄ (_▫₂_)
  private variable ⦃ comm₂ ⦄ : Commutativity ⦃ equiv-B ⦄ (_▫₂_)
  private variable ⦃ cancₗ₂ ⦄ : Cancellationₗ ⦃ equiv-B ⦄ ⦃ equiv-B ⦄ (_▫₂_)
  private variable ⦃ cancᵣ₂ ⦄ : Cancellationᵣ ⦃ equiv-B ⦄ ⦃ equiv-B ⦄ (_▫₂_)
  private variable ⦃ assoc₂ ⦄ : Associativity ⦃ equiv-B ⦄ (_▫₂_)
  private variable ⦃ ident₂  ⦄ : Identity ⦃ equiv-B ⦄ (_▫₂_)(id₂)
  private variable ⦃ identₗ₂ ⦄ : Identityₗ ⦃ equiv-B ⦄ (_▫₂_)(id₂)
  private variable ⦃ identᵣ₂ ⦄ : Identityᵣ ⦃ equiv-B ⦄ (_▫₂_)(id₂)
  private variable ⦃ inver₂  ⦄ : InverseFunction ⦃ equiv-B ⦄ (_▫₂_) ⦃ [∃]-intro(id₂) ⦃ ident₂ ⦄ ⦄ (inv₂)
  private variable ⦃ inverₗ₂ ⦄ : InverseFunctionₗ ⦃ equiv-B ⦄ (_▫₂_) ⦃ [∃]-intro(id₂) ⦃ identₗ₂ ⦄ ⦄ (inv₂)
  private variable ⦃ inverᵣ₂ ⦄ : InverseFunctionᵣ ⦃ equiv-B ⦄ (_▫₂_) ⦃ [∃]-intro(id₂) ⦃ identᵣ₂ ⦄ ⦄ (inv₂)

  module _ {θ : A → B} ⦃ func : Function ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ (θ) ⦄ (preserv : Names.Preserving₂ ⦃ equiv-B ⦄ (θ)(_▫₁_)(_▫₂_)) where
    preserving-identityₗ : let _ = cancᵣ₂ , select-idₗ(id₁)(identₗ₁) , select-idₗ(id₂)(identₗ₂) in (θ(id₁) ≡ id₂)
    preserving-identityₗ {id₁}{id₂} =
      (cancellationᵣ(_▫₂_)
        ((\{x} →
          (symmetry(_≡_) (preserv{id₁}{x})             :of: (θ(id₁) ▫₂ θ(x) ≡ θ(id₁ ▫₁ x)))
          🝖 ([≡]-with(θ) (identityₗ(_▫₁_)(id₁){x})     :of: (θ(id₁ ▫₁ x) ≡ θ(x)))
          🝖 (symmetry(_≡_)(identityₗ(_▫₂_)(id₂){θ(x)}) :of: (θ(x) ≡ id₂ ▫₂ θ(x)))
        ){id₁})
      )

    preserving-inverseₗ : let _ = cancᵣ₂ , select-invₗ(id₁)(identₗ₁)(inv₁)(inverₗ₁) , select-invₗ(id₂)(identₗ₂)(inv₂)(inverₗ₂) in ∀{x} → (θ(inv₁(x)) ≡ inv₂(θ(x)))
    preserving-inverseₗ {id₁}{inv₁}{id₂}{inv₂} {x} =
      (cancellationᵣ(_▫₂_)(
        (symmetry(_≡_) (preserv{inv₁(x)}{x})                 :of: (θ(inv₁(x)) ▫₂ θ(x) ≡ θ(inv₁(x) ▫₁ x)))
        🝖 ([≡]-with(θ) (inverseFunctionₗ(_▫₁_)(inv₁){x})     :of: (θ(inv₁(x) ▫₁ x) ≡ θ(id₁)))
        🝖 (preserving-identityₗ                              :of: (θ(id₁) ≡ id₂))
        🝖 (symmetry(_≡_)(inverseFunctionₗ(_▫₂_)(inv₂){θ(x)}) :of: (id₂ ≡ inv₂(θ(x)) ▫₂ θ(x)))
      ))

    preserving-identityᵣ : let _ = cancₗ₂ , select-idᵣ(id₁)(identᵣ₁) , select-idᵣ(id₂)(identᵣ₂) in (θ(id₁) ≡ id₂)
    preserving-identityᵣ {id₁}{id₂} =
      (cancellationₗ(_▫₂_)
        ((\{x} →
          (symmetry(_≡_)(preserv{x}{id₁})              :of: (θ(x) ▫₂ θ(id₁) ≡ θ(x ▫₁ id₁)))
          🝖 ([≡]-with(θ) (identityᵣ(_▫₁_)(id₁){x})     :of: (θ(x ▫₁ id₁) ≡ θ(x)))
          🝖 (symmetry(_≡_)(identityᵣ(_▫₂_)(id₂){θ(x)}) :of: (θ(x) ≡ θ(x) ▫₂ id₂))
        ){id₁})
      )

    preserving-inverseᵣ : let _ = cancₗ₂ , select-invᵣ(id₁)(identᵣ₁)(inv₁)(inverᵣ₁) , select-invᵣ(id₂)(identᵣ₂)(inv₂)(inverᵣ₂) in ∀{x} → (θ(inv₁(x)) ≡ inv₂(θ(x)))
    preserving-inverseᵣ {id₁}{inv₁}{id₂}{inv₂} {x} =
      (cancellationₗ(_▫₂_)(
        (symmetry(_≡_)(preserv{x}{inv₁(x)})                  :of: (θ(x) ▫₂ θ(inv₁(x)) ≡ θ(x ▫₁ inv₁(x))))
        🝖 ([≡]-with(θ) (inverseFunctionᵣ(_▫₁_)(inv₁){x})     :of: (θ(x ▫₁ inv₁(x)) ≡ θ(id₁)))
        🝖 (preserving-identityᵣ                              :of: (θ(id₁) ≡ id₂))
        🝖 (symmetry(_≡_)(inverseFunctionᵣ(_▫₂_)(inv₂){θ(x)}) :of: (id₂ ≡ θ(x) ▫₂ inv₂(θ(x))))
      ))

    injective-kernelᵣ : let _ = op₁ , op₂ , assoc₁ , assoc₂ , cancₗ₂ , select-inv(id₁)(ident₁)(inv₁)(inver₁) , select-inv(id₂)(ident₂)(inv₂)(inver₂) in Injective(θ) ↔ (∀{a} → (θ(a) ≡ id₂) → (a ≡ id₁))
    injective-kernelᵣ {id₁}{inv₁}{id₂}{inv₂} = [↔]-intro l (inj ↦ r ⦃ inj ⦄) where
      l : Injective(θ) ← (∀{a} → (θ(a) ≡ id₂) → (a ≡ id₁))
      Injective.proof(l(proof)) {a}{b} (θa≡θb) =
        One.equality-zeroₗ(
          proof(
            (preserv{a}{inv₁(b)}                                   :of: (θ(a ▫₁ inv₁(b)) ≡ θ(a) ▫₂ θ(inv₁(b))))
            🝖 ([≡]-with2ᵣ(_▫₂_)(θ(a)) (preserving-inverseᵣ{x = b}) :of: (θ(a) ▫₂ θ(inv₁(b)) ≡ θ(a) ▫₂ inv₂(θ(b))))
            🝖 (One.equality-zeroᵣ(θa≡θb)                           :of: (θ(a) ▫₂ inv₂(θ(b)) ≡ id₂))
          ) :of: (a ▫₁ inv₁(b) ≡ id₁)
        ) :of: (a ≡ b)

      r : ⦃ _ : Injective(θ) ⦄ → (∀{a} → (θ(a) ≡ id₂) → (a ≡ id₁))
      r {a} (θa≡id) =
        injective(θ) (
          θ(a)   🝖-[ θa≡id ]
          id₂    🝖-[ symmetry(_≡_) preserving-identityᵣ ]
          θ(id₁) 🝖-end
        )
