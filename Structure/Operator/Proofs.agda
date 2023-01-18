module Structure.Operator.Proofs where

import Lvl
open import Data
open import Data.Tuple
open import Functional hiding (id)
open import Function.Equals
import      Function.Names as Names
import      Lang.Vars.Structure.Operator
open        Lang.Vars.Structure.Operator.Select
open import Logic.IntroInstances
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Setoid.Uniqueness
open import Structure.Function.Domain
open import Structure.Function.Multi
open import Structure.Function
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Syntax.Type
open import Type

module One {ℓ ℓₑ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {_▫_ : T → T → T} where
  open Lang.Vars.Structure.Operator.One ⦃ equiv = equiv ⦄ {_▫_ = _▫_}

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
    idₗ ▫ a          🝖-[ congruence₂-₁(_▫_)(a) (symmetry(_≡_) (inverseFunctionₗ(_▫_)(invₗ) {x})) ]
    (invₗ x ▫ x) ▫ a 🝖-[ associativity(_▫_) {invₗ(x)}{x}{a} ]
    invₗ x ▫ (x ▫ a) 🝖-[ congruence₂-₂(_▫_)(invₗ(x)) (xa≡xb) ]
    invₗ x ▫ (x ▫ b) 🝖-[ symmetry(_≡_) (associativity(_▫_) {invₗ(x)}{x}{b}) ]
    (invₗ x ▫ x) ▫ b 🝖-[ congruence₂-₁(_▫_)(b) (inverseFunctionₗ(_▫_)(invₗ) {x}) ]
    idₗ ▫ b          🝖-[ identityₗ(_▫_)(idₗ){b} ]
    b                🝖-end
    -- TODO: This pattern of applying symmetric transitivity rules, make it a function

  -- Cancellation is possible when the operator is associative and have an inverse
  cancellationᵣ-by-associativity-inverse : let _ = op , assoc , inverᵣ in Cancellationᵣ(_▫_)
  Cancellationᵣ.proof(cancellationᵣ-by-associativity-inverse {idᵣ} {invᵣ} ) {x}{a}{b} (xa≡xb) =
    a                🝖-[ symmetry(_≡_) (identityᵣ(_▫_)(idᵣ)) ]
    a ▫ idᵣ          🝖-[ congruence₂-₂(_▫_)(_) (symmetry(_≡_) (inverseFunctionᵣ(_▫_)(invᵣ))) ]
    a ▫ (x ▫ invᵣ x) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
    (a ▫ x) ▫ invᵣ x 🝖-[ congruence₂-₁(_▫_)(_) (xa≡xb) ]
    (b ▫ x) ▫ invᵣ x 🝖-[ associativity(_▫_) ]
    b ▫ (x ▫ invᵣ x) 🝖-[ congruence₂-₂(_▫_)(_) (inverseFunctionᵣ(_▫_)(invᵣ)) ]
    b ▫ idᵣ          🝖-[ identityᵣ(_▫_)(idᵣ) ]
    b                🝖-end

  -- When something and something else's inverse is the identity element, they are equal
  equality-zero : let _ = op , assoc , select-inv(id)(ident)(inv)(inver) in ∀{x y} → (x ▫ inv(y) ≡ id) ↔ (x ≡ y)
  equality-zero {id}{inv} {x}{y} = [↔]-intro l r where
    r = \proof →
      x                🝖-[ symmetry(_≡_) (identity-right(_▫_)(id)) ]
      x ▫ id           🝖-[ symmetry(_≡_) (congruence₂-₂(_▫_)(x) (inverseFunction-left(_▫_)(inv))) ]
      x ▫ (inv(y) ▫ y) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
      (x ▫ inv(y)) ▫ y 🝖-[ congruence₂-₁(_▫_)(y) (proof) ]
      id ▫ y           🝖-[ identity-left(_▫_)(id) ]
      y                🝖-end

    l = \proof →
      x ▫ inv(y) 🝖-[ congruence₂-₁(_▫_)(inv(y)) proof ]
      y ▫ inv(y) 🝖-[ inverseFunctionᵣ(_▫_)(inv) ]
      id         🝖-end

  commuting-id : let _ = select-id(id)(ident) in ∀{x} → (id ▫ x ≡ x ▫ id)
  commuting-id {id} {x} =
    id ▫ x 🝖-[ identity-left(_▫_)(id) ]
    x      🝖-[ symmetry(_≡_) (identity-right(_▫_)(id)) ]
    x ▫ id 🝖-end

  squeezed-inverse : let _ = op , select-id(id)(ident) in ∀{a b x y} → (a ▫ b ≡ id) → ((x ▫ (a ▫ b)) ▫ y ≡ x ▫ y)
  squeezed-inverse {id} {a}{b}{x}{y} abid =
    (x ▫ (a ▫ b)) ▫ y 🝖-[ (congruence₂-₁(_▫_)(_) ∘ congruence₂-₂(_▫_)(_)) abid ]
    (x ▫ id) ▫ y      🝖-[ congruence₂-₁(_▫_)(_) (identity-right(_▫_)(id)) ]
    x ▫ y             🝖-end

  double-inverse : let _ = cancᵣ , select-inv(id)(ident)(inv)(inver) in ∀{x} → (inv(inv x) ≡ x)
  double-inverse {id}{inv} {x} =
    (cancellationᵣ(_▫_) $
      (
        inv(inv x) ▫ inv(x) 🝖-[ inverseFunction-left(_▫_)(inv) ]
        id                  🝖-[ inverseFunction-right(_▫_)(inv) ]-sym
        x ▫ inv(x)          🝖-end
      ) :of: (inv(inv x) ▫ inv(x) ≡ x ▫ inv(x))
    ) :of: (inv(inv x) ≡ x)

  double-inverseₗ-by-id : let _ = op , assoc , select-id(id)(ident) , select-invₗ(id)(Identity.left(ident))(invₗ)(inverₗ) in ∀{x} → (invₗ(invₗ x) ≡ x)
  double-inverseₗ-by-id {id}{inv} {x} =
    inv(inv(x))                🝖-[ symmetry(_≡_) (identityᵣ(_▫_)(id)) ]
    inv(inv(x)) ▫ id           🝖-[ congruence₂-₂(_▫_)(_) (symmetry(_≡_) (inverseFunctionₗ(_▫_)(inv))) ]
    inv(inv(x)) ▫ (inv(x) ▫ x) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
    (inv(inv(x)) ▫ inv(x)) ▫ x 🝖-[ congruence₂-₁(_▫_)(_) (inverseFunctionₗ(_▫_)(inv)) ]
    id ▫ x                     🝖-[ identityₗ(_▫_)(id) ]
    x                          🝖-end

  double-inverseᵣ-by-id : let _ = op , assoc , select-id(id)(ident) , select-invᵣ(id)(Identity.right(ident))(invᵣ)(inverᵣ) in ∀{x} → (invᵣ(invᵣ x) ≡ x)
  double-inverseᵣ-by-id {id}{inv} {x} =
    inv(inv(x))                🝖-[ identityₗ(_▫_)(id) ]-sym
    id ▫ inv(inv(x))           🝖-[ congruence₂-₁(_▫_)(_) (inverseFunctionᵣ(_▫_)(inv)) ]-sym
    (x ▫ inv(x)) ▫ inv(inv(x)) 🝖-[ associativity(_▫_) ]
    x ▫ (inv(x) ▫ inv(inv(x))) 🝖-[ congruence₂-₂(_▫_)(_) (inverseFunctionᵣ(_▫_)(inv)) ]
    x ▫ id                     🝖-[ identityᵣ(_▫_)(id) ]
    x                          🝖-end

  {- double-complement-by-?
  inv(inv(x)) ▫ inv(x)
  ab
  inv(x) ▫ x
  -}

  inverse-equivalence-by-id : let _ = op , assoc , select-id(id)(ident) in InverseFunctionₗ(_▫_)(inv) ↔ InverseFunctionᵣ(_▫_)(inv)
  inverse-equivalence-by-id {id}{inv} = [↔]-intro l r where
    l : InverseFunctionₗ(_▫_)(inv) ← InverseFunctionᵣ(_▫_)(inv)
    InverseFunctionₗ.proof (l inverᵣ) {x} =
      inv(x) ▫ x           🝖-[ congruence₂-₂(_▫_)(_) (symmetry(_≡_) (double-inverseᵣ-by-id ⦃ inverᵣ = inverᵣ ⦄)) ]
      inv(x) ▫ inv(inv(x)) 🝖-[ inverseFunctionᵣ(_▫_)(inv) ⦃ inverᵣ ⦄ ]
      id                   🝖-end
    r : InverseFunctionₗ(_▫_)(inv) → InverseFunctionᵣ(_▫_)(inv)
    InverseFunctionᵣ.proof (r inverₗ) {x} =
      x ▫ inv(x)           🝖-[ congruence₂-₁(_▫_)(_) (symmetry(_≡_) (double-inverseₗ-by-id ⦃ inverₗ = inverₗ ⦄)) ]
      inv(inv(x)) ▫ inv(x) 🝖-[ inverseFunctionₗ(_▫_)(inv) ⦃ inverₗ ⦄ ]
      id                   🝖-end

  {-
  complement-equivalence-by-id : let _ = op , assoc , select-abs(ab)(absorb) in ComplementFunctionₗ(_▫_)(inv) ↔ ComplementFunctionᵣ(_▫_)(inv)
  complement-equivalence-by-id {ab}{inv} = [↔]-intro l r where
    l : ComplementFunctionₗ(_▫_)(inv) ← ComplementFunctionᵣ(_▫_)(inv)
    ComplementFunctionₗ.proof (l absorbᵣ) {x} =
      inv(x) ▫ x           🝖-[ {!!} ]
      inv(x) ▫ inv(inv(x)) 🝖-[ {!!} ]
      ab                   🝖-end
    r : ComplementFunctionₗ(_▫_)(inv) → ComplementFunctionᵣ(_▫_)(inv)
    ComplementFunctionᵣ.proof (r absorbₗ) {x} =
      x ▫ inv(x)           🝖-[ {!!} ]
      inv(inv(x)) ▫ inv(x) 🝖-[ {!!} ]
      ab                   🝖-end
  -}

  cancellationₗ-by-group : let _ = op , assoc , select-invₗ(idₗ)(identₗ)(invₗ)(inverₗ) in Cancellationₗ(_▫_)
  Cancellationₗ.proof (cancellationₗ-by-group {id}{inv}) {a}{b}{c} abac =
    b                🝖-[ symmetry(_≡_) (identityₗ(_▫_)(id)) ]
    id ▫ b           🝖-[ congruence₂-₁(_▫_)(_) (symmetry(_≡_) (inverseFunctionₗ(_▫_)(inv))) ]
    (inv(a) ▫ a) ▫ b 🝖-[ associativity(_▫_) ]
    inv(a) ▫ (a ▫ b) 🝖-[ congruence₂-₂(_▫_)(_) abac ]
    inv(a) ▫ (a ▫ c) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
    (inv(a) ▫ a) ▫ c 🝖-[ congruence₂-₁(_▫_)(_) (inverseFunctionₗ(_▫_)(inv)) ]
    id ▫ c           🝖-[ identityₗ(_▫_)(id) ]
    c                🝖-end

  cancellationᵣ-by-group : let _ = op , assoc , select-invᵣ(idᵣ)(identᵣ)(invᵣ)(inverᵣ) in Cancellationᵣ(_▫_)
  Cancellationᵣ.proof (cancellationᵣ-by-group {id}{inv}) {c}{a}{b} acbc =
    a                🝖-[ symmetry(_≡_) (identityᵣ(_▫_)(id)) ]
    a ▫ id           🝖-[ congruence₂-₂(_▫_)(_) (symmetry(_≡_) (inverseFunctionᵣ(_▫_)(inv))) ]
    a ▫ (c ▫ inv(c)) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
    (a ▫ c) ▫ inv(c) 🝖-[ congruence₂-₁(_▫_)(_) acbc ]
    (b ▫ c) ▫ inv(c) 🝖-[ associativity(_▫_) ]
    b ▫ (c ▫ inv(c)) 🝖-[ congruence₂-₂(_▫_)(_) (inverseFunctionᵣ(_▫_)(inv)) ]
    b ▫ id           🝖-[ identityᵣ(_▫_)(id) ]
    b                🝖-end

  inverse-distribution : let _ = op , assoc , select-inv(id)(ident)(inv)(inver) in ∀{x y} → (inv(x ▫ y) ≡ inv(y) ▫ inv(x))
  inverse-distribution {id}{inv} {x}{y} =
    (cancellationᵣ(_▫_) ⦃ cancellationᵣ-by-group ⦄
      ((
        inv(x ▫ y) ▫ (x ▫ y)         🝖-[ inverseFunction-left(_▫_)(inv) ]
        id                           🝖-[ symmetry(_≡_) (inverseFunction-left(_▫_)(inv)) ]
        inv(y) ▫ y                   🝖-[ symmetry(_≡_) (squeezed-inverse (inverseFunction-left(_▫_)(inv))) ]
        (inv(y) ▫ (inv(x) ▫ x)) ▫ y  🝖-[ congruence₂-₁(_▫_)(_) (symmetry(_≡_) (associativity(_▫_))) ]
        ((inv(y) ▫ inv(x)) ▫ x) ▫ y  🝖-[ associativity(_▫_) ]
        (inv(y) ▫ inv(x)) ▫ (x ▫ y)  🝖-end
      ) :of: (inv(x ▫ y) ▫ (x ▫ y) ≡ (inv(y) ▫ inv(x)) ▫ (x ▫ y)))
    ) :of: (inv(x ▫ y) ≡ inv(y) ▫ inv(x))

  inverse-preserving : let _ = op , assoc , comm , select-inv(id)(ident)(inv)(inver) in Preserving₂(inv)(_▫_)(_▫_)
  Preserving.proof (inverse-preserving {id}{inv}) {x}{y} = inverse-distribution {id}{inv} {x}{y} 🝖 commutativity(_▫_)

  inverse-distribute-to-inverse : let _ = op , assoc , select-inv(id)(ident)(inv)(inver) in ∀{x y} → inv(inv x ▫ inv y) ≡ y ▫ x
  inverse-distribute-to-inverse {id}{inv} {x}{y} =
    inv(inv x ▫ inv y)      🝖-[ inverse-distribution ]
    inv(inv y) ▫ inv(inv x) 🝖-[ congruence₂-₂(_▫_)(_) (double-inverse ⦃ cancᵣ = cancellationᵣ-by-group ⦄) ]
    inv(inv y) ▫ x          🝖-[ congruence₂-₁(_▫_)(_) (double-inverse ⦃ cancᵣ = cancellationᵣ-by-group ⦄) ]
    y ▫ x                   🝖-end

  inverse-preserving-to-inverse : let _ = op , assoc , comm , select-inv(id)(ident)(inv)(inver) in ∀{x y} → inv(inv x ▫ inv y) ≡ x ▫ y
  inverse-preserving-to-inverse {id}{inv} {x}{y} = inverse-distribute-to-inverse {id}{inv} {x}{y} 🝖 commutativity(_▫_)

  unique-inverseₗ-by-id : let _ = op , assoc , select-id(id)(ident) , select-invₗ(id)(Identity.left ident)(inv)(inverₗ) in ∀{x x⁻¹} → (x⁻¹ ▫ x ≡ id) → (x⁻¹ ≡ inv(x))
  unique-inverseₗ-by-id {id = id} {inv = inv} {x}{x⁻¹} inver-elem =
    x⁻¹                          🝖-[ identityᵣ(_▫_)(id) ]-sym
    x⁻¹ ▫ id                     🝖-[ congruence₂-₂(_▫_)(_) (inverseFunctionₗ(_▫_)(inv)) ]-sym
    x⁻¹ ▫ (inv(inv(x)) ▫ inv(x)) 🝖-[ associativity(_▫_) ]-sym
    (x⁻¹ ▫ inv(inv(x))) ▫ inv(x) 🝖-[ congruence₂-₁(_▫_)(_) (congruence₂-₂(_▫_)(_) (double-inverseₗ-by-id)) ]
    (x⁻¹ ▫ x) ▫ inv(x)           🝖-[ congruence₂-₁(_▫_)(_) inver-elem ]
    id ▫ inv(x)                  🝖-[ identityₗ(_▫_)(id) ]
    inv(x)                       🝖-end

  unique-inverseᵣ-by-id : let _ = op , assoc , select-id(id)(ident) , select-invᵣ(id)(Identity.right ident)(inv)(inverᵣ) in ∀{x x⁻¹} → (x ▫ x⁻¹ ≡ id) → (x⁻¹ ≡ inv(x))
  unique-inverseᵣ-by-id {id = id} {inv = inv} {x}{x⁻¹} inver-elem =
    x⁻¹                          🝖-[ identityₗ(_▫_)(id) ]-sym
    id ▫ x⁻¹                     🝖-[ congruence₂-₁(_▫_)(_) (inverseFunctionᵣ(_▫_)(inv)) ]-sym
    (inv(x) ▫ inv(inv(x))) ▫ x⁻¹ 🝖-[ associativity(_▫_) ]
    inv(x) ▫ (inv(inv(x)) ▫ x⁻¹) 🝖-[ congruence₂-₂(_▫_)(_) (congruence₂-₁(_▫_)(_) double-inverseᵣ-by-id) ]
    inv(x) ▫ (x ▫ x⁻¹)           🝖-[ congruence₂-₂(_▫_)(_) inver-elem ]
    inv(x) ▫ id                  🝖-[ identityᵣ(_▫_)(id) ]
    inv(x)                       🝖-end

  unique-inverseFunctionₗ-by-id : let _ = op , assoc , select-id(id)(ident) in Unique(InverseFunctionₗ(_▫_))
  unique-inverseFunctionₗ-by-id {id = id} {x = inv₁} {inv₂} inverse₁ inverse₂ = intro \{x} → unique-inverseₗ-by-id ⦃ inverₗ = inverse₂ ⦄ (inverseFunctionₗ(_▫_)(inv₁) ⦃ inverse₁ ⦄)

  unique-inverseFunctionᵣ-by-id : let _ = op , assoc , select-id(id)(ident) in Unique(InverseFunctionᵣ(_▫_))
  unique-inverseFunctionᵣ-by-id {id = id} {x = inv₁} {inv₂} inverse₁ inverse₂ = intro \{x} → unique-inverseᵣ-by-id ⦃ inverᵣ = inverse₂ ⦄ (inverseFunctionᵣ(_▫_)(inv₁) ⦃ inverse₁ ⦄)

  unique-inverses : let _ = op , assoc , select-id(id)(ident) in ⦃ _ : InverseFunctionₗ(_▫_)(invₗ) ⦄ → ⦃ _ : InverseFunctionᵣ(_▫_)(invᵣ) ⦄ → (invₗ ≡ invᵣ)
  unique-inverses {id} {invₗ} {invᵣ} = intro \{x} →
    (
      invₗ(x)                 🝖-[ symmetry(_≡_) (identityᵣ(_▫_)(id)) ]
      invₗ(x) ▫ id            🝖-[ congruence₂-₂(_▫_)(_) (symmetry(_≡_) (inverseFunctionᵣ(_▫_)(invᵣ))) ]
      invₗ(x) ▫ (x ▫ invᵣ(x)) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
      (invₗ(x) ▫ x) ▫ invᵣ(x) 🝖-[ congruence₂-₁(_▫_)(_) (inverseFunctionₗ(_▫_)(invₗ)) ]
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

  cancellation-equivalence-by-commutativity : let _ = comm in Cancellationₗ(_▫_) ↔ Cancellationᵣ(_▫_)
  cancellation-equivalence-by-commutativity = [↔]-intro l r where
    r : Cancellationₗ(_▫_) → Cancellationᵣ(_▫_)
    Cancellationᵣ.proof (r cancₗ) {a}{b}{x} p = cancellationₗ _ ⦃ cancₗ ⦄ (commutativity(_▫_) 🝖 p 🝖 commutativity(_▫_))

    l : Cancellationₗ(_▫_) ← Cancellationᵣ(_▫_)
    Cancellationₗ.proof (l cancᵣ) {a}{b}{x} p = cancellationᵣ _ ⦃ cancᵣ ⦄ (commutativity(_▫_) 🝖 p 🝖 commutativity(_▫_))

  inverse-propertyₗ-by-groupₗ : let _ = op , assoc , select-invₗ(id)(identₗ)(inv)(inverₗ) in InversePropertyₗ(_▫_)(inv)
  InverseOperatorₗ.proof (inverse-propertyₗ-by-groupₗ {id = id}{inv = inv}) {x} {y} =
    inv(x) ▫ (x ▫ y) 🝖-[ associativity(_▫_) ]-sym
    (inv(x) ▫ x) ▫ y 🝖-[ congruence₂-₁(_▫_)(y) (inverseFunctionₗ(_▫_)(inv)) ]
    id ▫ y           🝖-[ identityₗ(_▫_)(id) ]
    y                🝖-end

  inverse-propertyᵣ-by-groupᵣ : let _ = op , assoc , select-invᵣ(id)(identᵣ)(inv)(inverᵣ) in InversePropertyᵣ(_▫_)(inv)
  InverseOperatorᵣ.proof (inverse-propertyᵣ-by-groupᵣ {id = id}{inv = inv}) {x} {y} =
    (x ▫ y) ▫ inv(y) 🝖-[ associativity(_▫_) ]
    x ▫ (y ▫ inv(y)) 🝖-[ congruence₂-₂(_▫_)(x) (inverseFunctionᵣ(_▫_)(inv)) ]
    x ▫ id           🝖-[ identityᵣ(_▫_)(id) ]
    x                🝖-end

  inverseᵣ-by-assoc-inv-propᵣ : let _ = op , assoc , select-idₗ(id)(identₗ) , select-invPropᵣ(inv)(inverPropᵣ) in InverseFunctionᵣ(_▫_) ⦃ [∃]-intro(id) ⦃ identᵣ ⦄ ⦄ (inv)
  InverseFunctionᵣ.proof (inverseᵣ-by-assoc-inv-propᵣ {id = id} {inv = inv}) {x} =
    x ▫ inv x        🝖-[ identityₗ(_▫_)(id) ]-sym
    id ▫ (x ▫ inv x) 🝖-[ associativity(_▫_) ]-sym
    (id ▫ x) ▫ inv x 🝖-[ inversePropᵣ(_▫_)(inv) ]
    id               🝖-end

  zero-when-redundant-addition : let _ = select-idₗ(id)(identₗ) , cancᵣ in ∀{x} → (x ≡ x ▫ x) → (x ≡ id)
  zero-when-redundant-addition {id = id} {x} p = cancellationᵣ(_▫_) $ symmetry(_≡_) $
    id ▫ x 🝖-[ identityₗ(_▫_)(id) ]
    x      🝖-[ p ]
    x ▫ x  🝖-end

  inv-of-id : let _ = select-id(id)(ident) , select-inv(id)(ident)(inv)(inver) in (inv(id) ≡ id)
  inv-of-id {id = id}{inv = inv} =
    inv id       🝖-[ identityₗ(_▫_)(id) ]-sym
    id ▫ inv(id) 🝖-[ inverseFunctionᵣ(_▫_)(inv) ]
    id           🝖-end

  inv-is-id : let _ = select-func ⦃ equiv ⦄ ⦃ equiv ⦄ (inv)(func) , select-id(id)(ident) , select-inv(id)(ident)(inv)(inver) , select-invol ⦃ equiv ⦄(inv)(invol) in ∀{x} → (inv(x) ≡ id) ↔ (x ≡ id)
  inv-is-id {inv = inv}{id = id}{x} = [↔]-intro
    (\xid →
      inv x  🝖[ _≡_ ]-[ congruence₁(inv) xid ]
      inv id 🝖[ _≡_ ]-[ inv-of-id ]
      id     🝖[ _≡_ ]-end
    )
    (\invxid →
      x          🝖[ _≡_ ]-[ involution(inv) ]-sym
      inv(inv x) 🝖[ _≡_ ]-[ congruence₁(inv) invxid ]
      inv id     🝖[ _≡_ ]-[ inv-of-id ]
      id         🝖-end
    )

module OneTypeTwoOp {ℓ ℓₑ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {_▫₁_ _▫₂_ : T → T → T} where
  open Lang.Vars.Structure.Operator.OneTypeTwoOp ⦃ equiv = equiv ⦄ {_▫₁_ = _▫₁_} {_▫₂_ = _▫₂_}

  absorptionₗ-by-abs-com-dist-id : let _ = op₁ , op₂ , distriₗ , select-absₗ(id)(absorbₗ₂) , select-idᵣ(id)(identᵣ₁) in Absorptionₗ(_▫₂_)(_▫₁_)
  Absorptionₗ.proof (absorptionₗ-by-abs-com-dist-id {id = id}) {x}{y} =
    x ▫₂ (x ▫₁ y)         🝖-[ congruence₂-₁(_▫₂_)(_) (identityᵣ(_▫₁_)(id)) ]-sym
    (x ▫₁ id) ▫₂ (x ▫₁ y) 🝖-[ distributivityₗ(_▫₁_)(_▫₂_) ]-sym
    x ▫₁ (id ▫₂ y)        🝖-[ congruence₂-₂(_▫₁_)(_) (absorberₗ(_▫₂_)(id)) ]
    x ▫₁ id               🝖-[ identityᵣ(_▫₁_)(id) ]
    x                     🝖-end

  absorptionᵣ-by-abs-com-dist-id : let _ = op₁ , op₂ , distriᵣ , select-absᵣ(id)(absorbᵣ₂) , select-idₗ(id)(identₗ₁) in Absorptionᵣ(_▫₂_)(_▫₁_)
  Absorptionᵣ.proof (absorptionᵣ-by-abs-com-dist-id {id = id}) {x}{y} =
    (x ▫₁ y) ▫₂ y         🝖-[ congruence₂-₂(_▫₂_)(_) (identityₗ(_▫₁_)(id)) ]-sym
    (x ▫₁ y) ▫₂ (id ▫₁ y) 🝖-[ distributivityᵣ(_▫₁_)(_▫₂_) ]-sym
    (x ▫₂ id) ▫₁ y        🝖-[ congruence₂-₁(_▫₁_)(_) (absorberᵣ(_▫₂_)(id)) ]
    id ▫₁ y               🝖-[ identityₗ(_▫₁_)(id) ]
    y                     🝖-end

  distributivity-equivalence-by-commutativity : let _ = op₂ , comm₁ in Distributivityₗ(_▫₁_)(_▫₂_) ↔ Distributivityᵣ(_▫₁_)(_▫₂_)
  distributivity-equivalence-by-commutativity = [↔]-intro l r where
    l : Distributivityₗ(_▫₁_)(_▫₂_) ← Distributivityᵣ(_▫₁_)(_▫₂_)
    Distributivityₗ.proof (l distriᵣ) {x}{y}{z} =
      x ▫₁ (y ▫₂ z)        🝖-[ commutativity(_▫₁_) ]
      (y ▫₂ z) ▫₁ x        🝖-[ distributivityᵣ(_▫₁_)(_▫₂_) ⦃ distriᵣ ⦄ ]
      (y ▫₁ x) ▫₂ (z ▫₁ x) 🝖-[ congruence₂-₁(_▫₂_)(_) (commutativity(_▫₁_)) ]
      (x ▫₁ y) ▫₂ (z ▫₁ x) 🝖-[ congruence₂-₂(_▫₂_)(_) (commutativity(_▫₁_)) ]
      (x ▫₁ y) ▫₂ (x ▫₁ z) 🝖-end

    r : Distributivityₗ(_▫₁_)(_▫₂_) → Distributivityᵣ(_▫₁_)(_▫₂_)
    Distributivityᵣ.proof (r distriₗ) {x}{y}{z} =
      (x ▫₂ y) ▫₁ z        🝖-[ commutativity(_▫₁_) ]
      z ▫₁ (x ▫₂ y)        🝖-[ distributivityₗ(_▫₁_)(_▫₂_) ⦃ distriₗ ⦄ ]
      (z ▫₁ x) ▫₂ (z ▫₁ y) 🝖-[ congruence₂-₁(_▫₂_)(_) (commutativity(_▫₁_)) ]
      (x ▫₁ z) ▫₂ (z ▫₁ y) 🝖-[ congruence₂-₂(_▫₂_)(_) (commutativity(_▫₁_)) ]
      (x ▫₁ z) ▫₂ (y ▫₁ z) 🝖-end

  absorption-equivalence-by-commutativity : let _ = op₁ , comm₁ , comm₂ in Absorptionₗ(_▫₁_)(_▫₂_) ↔ Absorptionᵣ(_▫₁_)(_▫₂_)
  absorption-equivalence-by-commutativity = [↔]-intro l r where
    r : Absorptionₗ(_▫₁_)(_▫₂_) → Absorptionᵣ(_▫₁_)(_▫₂_)
    Absorptionᵣ.proof (r absorpₗ) {x}{y} =
      (x ▫₂ y) ▫₁ y 🝖-[ commutativity(_▫₁_) ]
      y ▫₁ (x ▫₂ y) 🝖-[ congruence₂-₂(_▫₁_)(_) (commutativity(_▫₂_)) ]
      y ▫₁ (y ▫₂ x) 🝖-[ absorptionₗ(_▫₁_)(_▫₂_) ⦃ absorpₗ ⦄ {y}{x} ]
      y             🝖-end

    l : Absorptionₗ(_▫₁_)(_▫₂_) ← Absorptionᵣ(_▫₁_)(_▫₂_)
    Absorptionₗ.proof (l absorpᵣ) {x}{y} =
      x ▫₁ (x ▫₂ y) 🝖-[ commutativity(_▫₁_) ]
      (x ▫₂ y) ▫₁ x 🝖-[ congruence₂-₁(_▫₁_)(_) (commutativity(_▫₂_)) ]
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

  distributeₗ-inv : let _ = op₁ , op₂ , assoc₂ , distriᵣ , select-inv(id₂)(ident₂)(inv₂)(inver₂) , select-absₗ(id₂)(absorbₗ₁) in ∀{x y} → (inv₂(x) ▫₁ y ≡ inv₂(x ▫₁ y))
  distributeₗ-inv {id₂ = id₂}{inv₂ = inv₂} {x}{y} = One.unique-inverseᵣ-by-id $
    (x ▫₁ y) ▫₂ (inv₂(x) ▫₁ y) 🝖-[ distributivityᵣ(_▫₁_)(_▫₂_) ]-sym
    (x ▫₂ inv₂(x)) ▫₁ y        🝖-[ congruence₂-₁(_▫₁_)(y) (inverseFunctionᵣ(_▫₂_)(inv₂)) ]
    id₂ ▫₁ y                   🝖-[ absorberₗ(_▫₁_)(id₂) ]
    id₂                        🝖-end

  distributeᵣ-inv :  let _ = op₁ , op₂ , assoc₂ , distriₗ , select-inv(id₂)(ident₂)(inv₂)(inver₂) , select-absᵣ(id₂)(absorbᵣ₁) in ∀{x y} → (x ▫₁ inv₂(y) ≡ inv₂(x ▫₁ y))
  distributeᵣ-inv {id₂ = id₂}{inv₂ = inv₂} {x}{y} = One.unique-inverseᵣ-by-id $
    (x ▫₁ y) ▫₂ (x ▫₁ inv₂(y)) 🝖-[ distributivityₗ(_▫₁_)(_▫₂_) ]-sym
    x ▫₁ (y ▫₂ inv₂(y))        🝖-[ congruence₂-₂(_▫₁_)(x) (inverseFunctionᵣ(_▫₂_)(inv₂)) ]
    x ▫₁ id₂                   🝖-[ absorberᵣ(_▫₁_)(id₂) ]
    id₂                        🝖-end

  op-on-inv-cancel : let _ = op₁ , op₂ , assoc₂ , distriₗ , distriᵣ , select-inv(id₂)(ident₂)(inv₂)(inver₂) , select-absₗ(id₂)(absorbₗ₁) , select-absᵣ(id₂)(absorbᵣ₁) , select-invol ⦃ equiv ⦄(inv₂)(invol) , select-func ⦃ equiv ⦄ ⦃ equiv ⦄ (inv₂)(func) in ∀{x y} → (inv₂(x) ▫₁ inv₂(y) ≡ x ▫₁ y)
  op-on-inv-cancel {id₂ = id₂}{inv₂ = inv₂} {x}{y} =
    (inv₂(x) ▫₁ inv₂(y)) 🝖[ _≡_ ]-[ distributeᵣ-inv ]
    inv₂(inv₂(x) ▫₁ y)   🝖[ _≡_ ]-[ congruence₁(inv₂) distributeₗ-inv ]
    inv₂(inv₂(x ▫₁ y))   🝖[ _≡_ ]-[ involution(inv₂) ]
    (x ▫₁ y)             🝖-end

  cancellationₗ-by-inverseOper : let _ = op₂ , inverOpₗ in Cancellationₗ(_▫₁_)
  Cancellationₗ.proof cancellationₗ-by-inverseOper {x}{a}{b} (xa≡xb) =
    a             🝖-[ inverseOperₗ(_▫₁_)(_▫₂_) ]-sym
    x ▫₂ (x ▫₁ a) 🝖-[ congruence₂-₂(_▫₂_)(x) (xa≡xb) ]
    x ▫₂ (x ▫₁ b) 🝖-[ inverseOperₗ(_▫₁_)(_▫₂_) ]
    b             🝖-end

  cancellationᵣ-by-inverseOper : let _ = op₂ , inverOpᵣ in Cancellationᵣ(_▫₁_)
  Cancellationᵣ.proof cancellationᵣ-by-inverseOper {x}{a}{b} (ax≡bx) =
    a             🝖-[ inverseOperᵣ(_▫₁_)(_▫₂_) ]-sym
    (a ▫₁ x) ▫₂ x 🝖-[ congruence₂-₁(_▫₂_)(x) (ax≡bx) ]
    (b ▫₁ x) ▫₂ x 🝖-[ inverseOperᵣ(_▫₁_)(_▫₂_) ]
    b             🝖-end

module Two {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂} {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ {_▫₁_ : A → A → A} {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ {_▫₂_ : B → B → B} where
  open Lang.Vars.Structure.Operator.Two ⦃ equiv-A = equiv-A ⦄ {_▫₁_ = _▫₁_} ⦃ equiv-B = equiv-B ⦄ {_▫₂_ = _▫₂_}

  module _ {θ : A → B} ⦃ func : Function ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ (θ) ⦄ ⦃ preserv : Preserving₂ ⦃ equiv-B ⦄ (θ)(_▫₁_)(_▫₂_) ⦄ where
    preserving-identityₗ : let _ = cancᵣ₂ , select-idₗ(id₁)(identₗ₁) , select-idₗ(id₂)(identₗ₂) in (θ(id₁) ≡ id₂)
    preserving-identityₗ {id₁}{id₂} = cancellationᵣ(_▫₂_) $
      θ(id₁) ▫₂ θ(id₁) 🝖-[ preserving₂(θ)(_▫₁_)(_▫₂_) ]-sym
      θ(id₁ ▫₁ id₁)    🝖-[ congruence₁(θ) (identityₗ(_▫₁_)(id₁)) ]
      θ(id₁)           🝖-[ identityₗ(_▫₂_)(id₂) ]-sym
      id₂ ▫₂ θ(id₁)    🝖-end

    preserving-inverseₗ : let _ = cancᵣ₂ , select-invₗ(id₁)(identₗ₁)(inv₁)(inverₗ₁) , select-invₗ(id₂)(identₗ₂)(inv₂)(inverₗ₂) in ∀{x} → (θ(inv₁(x)) ≡ inv₂(θ(x)))
    preserving-inverseₗ {id₁}{inv₁}{id₂}{inv₂} {x} = cancellationᵣ(_▫₂_) $
      θ(inv₁ x) ▫₂ θ(x)  🝖-[ preserving₂(θ)(_▫₁_)(_▫₂_) ]-sym
      θ(inv₁ x ▫₁ x)     🝖-[ congruence₁(θ) (inverseFunctionₗ(_▫₁_)(inv₁)) ]
      θ(id₁)             🝖-[ preserving-identityₗ ]
      id₂                🝖-[ inverseFunctionₗ(_▫₂_)(inv₂) ]-sym
      inv₂(θ(x)) ▫₂ θ(x) 🝖-end

    preserving-identityᵣ : let _ = cancₗ₂ , select-idᵣ(id₁)(identᵣ₁) , select-idᵣ(id₂)(identᵣ₂) in (θ(id₁) ≡ id₂)
    preserving-identityᵣ {id₁}{id₂} = cancellationₗ(_▫₂_) $
      θ(id₁) ▫₂ θ(id₁) 🝖-[ preserving₂(θ)(_▫₁_)(_▫₂_) ]-sym
      θ(id₁ ▫₁ id₁)    🝖-[ congruence₁(θ) (identityᵣ(_▫₁_)(id₁)) ]
      θ(id₁)           🝖-[ identityᵣ(_▫₂_)(id₂) ]-sym
      θ(id₁) ▫₂ id₂    🝖-end

    preserving-inverseᵣ : let _ = cancₗ₂ , select-invᵣ(id₁)(identᵣ₁)(inv₁)(inverᵣ₁) , select-invᵣ(id₂)(identᵣ₂)(inv₂)(inverᵣ₂) in ∀{x} → (θ(inv₁(x)) ≡ inv₂(θ(x)))
    preserving-inverseᵣ {id₁}{inv₁}{id₂}{inv₂} {x} = cancellationₗ(_▫₂_) $
      θ(x) ▫₂ θ(inv₁(x)) 🝖-[ preserving₂(θ)(_▫₁_)(_▫₂_) ]-sym
      θ(x ▫₁ inv₁(x))    🝖-[ congruence₁(θ) (inverseFunctionᵣ(_▫₁_)(inv₁)) ]
      θ(id₁)             🝖-[ preserving-identityᵣ ]
      id₂                🝖-[ inverseFunctionᵣ(_▫₂_)(inv₂) ]-sym
      θ(x) ▫₂ inv₂(θ(x)) 🝖-end

    injective-kernel : let _ = op₁ , op₂ , assoc₁ , assoc₂ , cancₗ₂ , select-inv(id₁)(ident₁)(inv₁)(inver₁) , select-inv(id₂)(ident₂)(inv₂)(inver₂) in Injective(θ) ↔ (∀{a} → (θ(a) ≡ id₂) → (a ≡ id₁))
    injective-kernel {id₁}{inv₁}{id₂}{inv₂} = [↔]-intro l (\inj → r ⦃ inj ⦄) where
      l : Injective(θ) ← (∀{a} → (θ(a) ≡ id₂) → (a ≡ id₁))
      Injective.proof(l(proof)) {a}{b} (θa≡θb) =
        [↔]-to-[→] One.equality-zero(
          proof(
            θ (a ▫₁ inv₁(b))   🝖-[ preserving₂(θ)(_▫₁_)(_▫₂_) ]
            θ(a) ▫₂ θ(inv₁(b)) 🝖-[ congruence₂-₂(_▫₂_)(θ(a)) preserving-inverseᵣ ]
            θ(a) ▫₂ inv₂(θ(b)) 🝖-[ [↔]-to-[←] One.equality-zero(θa≡θb) ]
            id₂                🝖-end
          ) :of: (a ▫₁ inv₁(b) ≡ id₁)
        ) :of: (a ≡ b)

      r : ⦃ _ : Injective(θ) ⦄ → (∀{a} → (θ(a) ≡ id₂) → (a ≡ id₁))
      r {a} (θa≡id) = injective(θ) $
        θ(a)   🝖-[ θa≡id ]
        id₂    🝖-[ preserving-identityᵣ ]-sym
        θ(id₁) 🝖-end
