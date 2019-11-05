module Functional.Repeat.Proofs where

import Lvl
open import Functional
open import Functional.Names as Names using (_⊜_)
open import Functional.Repeat
open import Functional.Proofs
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper using (_+_ ; _⋅_)
open import Numeral.Natural.Oper.Proofs
open import Structure.Operator.Properties
open import Structure.Operator.Proofs
import      Structure.Operator.Names as Names
open import Structure.Relator.Properties
open import Structure.Function.Domain hiding (Function)
open import Syntax.Transitivity
open import Type

module _ where
  open import Sets.Setoid

  module _ {ℓ} {X : Type{ℓ}} ⦃ _ : Equiv(X) ⦄ where
    -- Propositions that state something about arbitrary composed functions also apply to arbitrary function iterations of the first function.
    [^]-from-[∘]-proof : ∀{ℓ₂}{P : (X → X) → Type{ℓ₂}} → (∀{f g : X → X} → P(f ∘ g)) → (∀{f : X → X}{n} → P(f ^ n))
    [^]-from-[∘]-proof {P = P} p {f} {𝟎}   = p{id}{id}
    [^]-from-[∘]-proof {P = P} p {f} {𝐒 n} = p{f}{f ^ n}

    [^]-injective-raw : ∀{f : X → X} → Names.Injective(f) → ∀{n} → Names.Injective(f ^ n)
    [^]-injective-raw inj-f {𝟎}    fnxfny = fnxfny
    [^]-injective-raw inj-f {𝐒(n)} fnxfny = [^]-injective-raw inj-f {n} (inj-f fnxfny)

    -- Iterated function is injective when the function is.
    [^]-injective : ∀{f : X → X} → ⦃ _ : Injective(f) ⦄ → ∀{n} → Injective(f ^ n)
    Injective.proof ([^]-injective ⦃ intro inj-f ⦄ {n}) = [^]-injective-raw inj-f {n}

    [^]-surjective-raw : ∀{f : X → X} → ⦃ _ : Function(f) ⦄ → Names.Surjective(f) → ∀{n} → Names.Surjective(f ^ n)
    [^]-surjective-raw     surj-f {𝟎}    {y} = [∃]-intro y ⦃ reflexivity(_≡_) ⦄
    [^]-surjective-raw {f} surj-f {𝐒(n)} {y} = [∃]-map-proof (p ↦ ([≡]-with(f) p) 🝖 [∃]-proof(surj-f {y})) ([^]-surjective-raw surj-f {n} {[∃]-witness(surj-f {y})})

    -- Iterated function is surjective when the function is.
    [^]-surjective : ∀{f : X → X} → ⦃ _ : Function(f) ⦄ → ⦃ _ : Surjective(f) ⦄ → ∀{n} → Surjective(f ^ n)
    Surjective.proof ([^]-surjective ⦃ _ ⦄ ⦃ intro surj-f ⦄ {n}) = [^]-surjective-raw surj-f {n}

    -- Argument applied to the iterated function is one extra iteration.
    -- Note: This implies: (f ^ n)(f x) ≡ f((f ^ n)(x))
    [^]-inner-value : ∀{f : X → X} → ⦃ _ : Function(f) ⦄ → ∀{x}{n} → ((f ^ n)(f x) ≡ (f ^ (𝐒(n)))(x))
    [^]-inner-value {f} {x} {𝟎}   = reflexivity(_≡_)
    [^]-inner-value {f} {x} {𝐒 n} = [≡]-with(f) ([^]-inner-value {f} {x} {n})

    -- A fixpoint of the function is also a fixpoint of the iterated function.
    [^]-of-fixpoint : ∀{f : X → X} → ⦃ _ : Function(f) ⦄ → ∀{x : X} → ⦃ _ : Fixpoint f(x) ⦄ → ∀{n} → ((f ^ n)(x) ≡ x)
    [^]-of-fixpoint {f} {x} {𝟎}    = reflexivity(_≡_)
    [^]-of-fixpoint {f} {x} {𝐒(n)} =
      (f ^ 𝐒(n))(x)    🝖-[ reflexivity(_≡_) ]
      (f ∘ (f ^ n))(x) 🝖-[ reflexivity(_≡_) ]
      f((f ^ n)(x))    🝖-[ [≡]-with(f) ([^]-of-fixpoint {f} {x} {n}) ]
      f(x)             🝖-[ fixpoint f(x) ]
      x                🝖-end

  module _ {ℓ} {X : Type{ℓ}} ⦃ _ : Equiv(X → X) ⦄ where
    [^]-by-1 : ∀{f : X → X} → (f ^ 1 ≡ f)
    [^]-by-1 {f} = reflexivity(_≡_)

    [^]-of-id : ∀{n} → (id ^ n ≡ id)
    [^]-of-id {𝟎}   = reflexivity(_≡_)
    [^]-of-id {𝐒 n} = [^]-of-id {n}

    [^]-inner : ∀{f : X → X} → ⦃ _ : Function(f ∘_) ⦄ → ∀{n} → ((f ^ n) ∘ f ≡ f ^ (𝐒(n)))
    [^]-inner {f} {𝟎}   = reflexivity(_≡_)
    [^]-inner {f} {𝐒 n} = [≡]-with(f ∘_) ([^]-inner {f} {n})

    [^]-add : ⦃ [∘]-op : BinaryOperator(_∘_) ⦄ → ∀{f : X → X} → ∀{a b} → ((f ^ a) ∘ (f ^ b) ≡ f ^ (a + b))
    [^]-add {f} {𝟎} {𝟎}     = reflexivity(_≡_)
    [^]-add {f} {𝟎} {𝐒 b}   = reflexivity(_≡_)
    [^]-add {f} {𝐒 a} {𝟎}   = reflexivity(_≡_)
    [^]-add ⦃ [∘]-op ⦄ {f} {𝐒 a} {𝐒 b} =
      (f ^ 𝐒(a)) ∘ (f ^ 𝐒(b))    🝖-[ reflexivity(_≡_) ]
      (f ^ 𝐒(a)) ∘ (f ∘ (f ^ b)) 🝖-[ reflexivity(_≡_) ]
      ((f ^ 𝐒(a)) ∘ f) ∘ (f ^ b) 🝖-[ [≡]-with2ₗ(_∘_)(f ^ b) ([^]-inner {f} ⦃ [≡]-congruence2-right(_∘_)(f) ⦄ {𝐒(a)}) ]
      f ∘ ((f ^ 𝐒(a)) ∘ (f ^ b)) 🝖-[ reflexivity(_≡_) ]
      (f ∘ (f ^ 𝐒(a))) ∘ (f ^ b) 🝖-[ [≡]-with2ᵣ(_∘_)(f) ([^]-add{f} {𝐒 a} {b}) ]
      f ∘ (f ^ (𝐒(a) + b))       🝖-[ reflexivity(_≡_) ]
      f ^ (𝐒(a) + 𝐒(b))          🝖-end

    [^]-multiply : ⦃ [∘]-op : BinaryOperator(_∘_) ⦄ → ∀{f : X → X} → ∀{a b} → ((f ^ a) ^ b ≡ f ^ (a ⋅ b))
    [^]-multiply ⦃ [∘]-op ⦄ {f} {𝟎}   {𝟎}   = reflexivity(_≡_)
    [^]-multiply ⦃ [∘]-op ⦄ {f} {𝟎}   {𝐒 b} = [^]-of-id {𝐒 b}
    [^]-multiply ⦃ [∘]-op ⦄ {f} {𝐒 a} {𝟎}   = reflexivity(_≡_)
    [^]-multiply ⦃ [∘]-op ⦄ {f} {𝐒 a} {𝐒 b} =
      (f ^ 𝐒(a)) ^ 𝐒(b)             🝖-[ reflexivity(_≡_) ]
      (f ^ 𝐒(a)) ∘ ((f ^ 𝐒(a)) ^ b) 🝖-[ [≡]-with2ᵣ(_∘_)(f ^ 𝐒(a)) ([^]-multiply{f} {𝐒 a} {b}) ]
      (f ^ 𝐒(a)) ∘ (f ^ (𝐒(a) ⋅ b)) 🝖-[ [^]-add {f} {𝐒(a)} {𝐒(a) ⋅ b} ]
      f ^ (𝐒(a) + (𝐒(a) ⋅ b))       🝖-[ reflexivity(_≡_) ]
      f ^ (𝐒(a) ⋅ 𝐒(b))             🝖-end

    module _ ⦃ op : BinaryOperator(_∘_) ⦄ ⦃ _ : Associativity(_∘_) ⦄ where
      [^]-commuting : ∀{f g : X → X} → Names.Commuting(_∘_)(f)(g) → ∀{a b} → Names.Commuting(_∘_)(f ^ a)(g ^ b)
      [^]-commuting {f} {g} com {𝟎}   {𝟎}   = reflexivity(_≡_)
      [^]-commuting {f} {g} com {𝟎}   {𝐒 b} = reflexivity(_≡_)
      [^]-commuting {f} {g} com {𝐒 a} {𝟎}   = reflexivity(_≡_)
      [^]-commuting {f} {g} com {𝐒 a} {𝐒 b} =
        (f ^ 𝐒(a)) ∘ (g ^ 𝐒(b))       🝖-[ reflexivity(_≡_) ]
        (f ∘ (f ^ a)) ∘ (g ∘ (g ^ b)) 🝖-[ One.associate-commute4 {a = f} {f ^ a} {g} {g ^ b} ([^]-commuting {f} {g} com {a} {1}) ]
        (f ∘ g) ∘ ((f ^ a) ∘ (g ^ b)) 🝖-[ [≡]-with2(_∘_) com ([^]-commuting {f} {g} com {a} {b}) ]
        (g ∘ f) ∘ ((g ^ b) ∘ (f ^ a)) 🝖-[ One.associate-commute4 {a = g} {f} {g ^ b} {f ^ a} ([^]-commuting {f} {g} com {1} {b}) ]
        (g ∘ (g ^ b)) ∘ (f ∘ (f ^ a)) 🝖-[ reflexivity(_≡_) ]
        (g ^ 𝐒(b)) ∘ (f ^ 𝐒(a))       🝖-end

      [^]-of-[∘] :  ∀{f : X → X}{g : X → X} → Names.Commuting(_∘_)(f)(g) → ∀{n} → ((f ∘ g) ^ n ≡ (f ^ n) ∘ (g ^ n))
      [^]-of-[∘] {f}{g} com {𝟎}   = reflexivity(_≡_)
      [^]-of-[∘] {f}{g} com {𝐒 n} =
        (f ∘ g) ^ 𝐒(n)                🝖-[ reflexivity(_≡_) ]
        (f ∘ g) ∘ ((f ∘ g) ^ n)       🝖-[ [≡]-with2ᵣ(_∘_)(f ∘ g) ([^]-of-[∘] {f}{g} com {n}) ]
        (f ∘ g) ∘ ((f ^ n) ∘ (g ^ n)) 🝖-[ One.associate-commute4 {a = f} {g} {f ^ n}{g ^ n} (symmetry(_≡_) ([^]-commuting {f} {g} com {n} {1})) ]
        (f ∘ (f ^ n)) ∘ (g ∘ (g ^ n)) 🝖-[ reflexivity(_≡_) ]
        (f ^ 𝐒(n)) ∘ (g ^ 𝐒(n))       🝖-end

module _ {ℓ₁}{ℓ₂} {X : Type{ℓ₁}} {Y : Type{ℓ₂}} where
  open import Relator.Equals
  open import Relator.Equals.Proofs

  repeatᵣₗ-flip-equality : ∀{n : ℕ}{_▫_ : Y → X → Y}{init : Y}{x : X} → (repeatᵣ n (swap(_▫_)) x init ≡ repeatₗ n (_▫_) init x)
  repeatᵣₗ-flip-equality {𝟎}               = [≡]-intro
  repeatᵣₗ-flip-equality {𝐒(n)}{_▫_}{_}{x} = [≡]-with(_▫ x) (repeatᵣₗ-flip-equality {n}{_▫_})

  repeatₗᵣ-flip-equality : ∀{n : ℕ}{_▫_ : X → Y → Y}{x : X}{init : Y} → (repeatₗ n (swap _▫_) init x ≡ repeatᵣ n (_▫_) x init)
  repeatₗᵣ-flip-equality {n}{_▫_}{x}{init} = symmetry(_≡_) (repeatᵣₗ-flip-equality {n}{swap _▫_}{init}{x})

module _ {ℓ} {X : Type{ℓ}} where
  open import Relator.Equals
  open import Relator.Equals.Proofs

  [^]-from-repeatᵣ-alt : ∀{f : X → X}{n} → ((f ^ n) ⊜ repeatᵣ(n) (f ∘_) id)
  [^]-from-repeatᵣ-alt    {n = 𝟎}   = [≡]-intro
  [^]-from-repeatᵣ-alt {f}{n = 𝐒 n} = [≡]-with(f) ([^]-from-repeatᵣ-alt {n = n})

  [^]-from-repeatᵣ : ∀{f : X → X}{n} → ((f ^ n) ⊜ repeatᵣ(n) (_∘_) f id)
  [^]-from-repeatᵣ    {n = 𝟎}   = [≡]-intro
  [^]-from-repeatᵣ {f}{n = 𝐒 n} = [≡]-with(f) ([^]-from-repeatᵣ {f}{n = n})

  -- TODO: Should also be provable using associativity? Prove (CommutingOn(_▫_)(x)(x) → AssociativityOn(_▫_)(x)). Is this helping?
  repeat-swap-side : ∀{n : ℕ}{_▫_ : X → X → X}{x : X} → ⦃ _ : Commutativity(_▫_) ⦄ → (repeatₗ n (_▫_) x x ≡ repeatᵣ n (_▫_) x x)
  repeat-swap-side {𝟎}   = [≡]-intro
  repeat-swap-side {𝐒 n}{_▫_}{x} = [≡]-with(_▫ x) (repeat-swap-side {n}) 🝖 commutativity(_▫_)

  {-
  repeat-swap-side-by-associativity : ∀{n : ℕ}{_▫_ : X → X → X}{x : X} → ⦃ _ : Associativity(_▫_) ⦄ → (repeatₗ n (_▫_) x x ≡ repeatᵣ n (_▫_) x x)
  repeat-swap-side-by-associativity {𝟎}   = [≡]-intro
  repeat-swap-side-by-associativity {𝐒 n}{_▫_}{x} = {!repeat-swap-side-by-associativity {n}{_▫_}{x}!}
  -}

  repeat-with-id-swap-side : ∀{n : ℕ}{_▫_ : X → X → X}{x init : X} → ⦃ _ : Commutativity(_▫_) ⦄ ⦃ _ : Identity(_▫_)(init) ⦄ → (repeatₗ n (_▫_) init x ≡ repeatᵣ n (_▫_) x init)
  repeat-with-id-swap-side {𝟎} = [≡]-intro
  repeat-with-id-swap-side {𝐒 n}{_▫_}{x} ⦃ comm ⦄ ⦃ ident ⦄ = [≡]-with(_▫ x) (repeat-with-id-swap-side {n} ⦃ comm ⦄ ⦃ ident ⦄) 🝖 commutativity(_▫_)

  repeat-raise-equality : ∀{n : ℕ}{_▫_ : X → X → X}{elem x : X} → (repeatᵣ n (_▫_) elem (x) ≡ ((elem ▫_) ^ n)(x))
  repeat-raise-equality{𝟎}                  = [≡]-intro
  repeat-raise-equality{𝐒(n)}{_▫_}{elem}{x} = [≡]-with(elem ▫_) (repeat-raise-equality{n}{_▫_}{elem}{x})

  raise-repeat-equality : ∀{n : ℕ}{f : X → X} → (f ^ n ≡ repeatᵣ n (_∘_) f id)
  raise-repeat-equality{𝟎}       = [≡]-intro
  raise-repeat-equality{𝐒(n)}{f} = [≡]-with(f ∘_) (raise-repeat-equality{n}{f})
module _ where
  open import Functional.Equals
  open import Sets.Setoid

  module _ {ℓ} {X : Type{ℓ}} ⦃ equiv-X : Equiv(X) ⦄ where
    repeatₗ-by-0 : ∀{_▫_ : X → X → X}{x id} → ⦃ _ : Identityᵣ(_▫_)(id) ⦄ → (repeatᵣ 0 (_▫_) x id ≡ id)
    repeatₗ-by-0 {_▫_} {x}{id} ⦃ identᵣ ⦄ = reflexivity(_≡_)

    repeatₗ-by-1 : ∀{_▫_ : X → X → X}{x id} → ⦃ _ : Identityᵣ(_▫_)(id) ⦄ → (repeatᵣ 1 (_▫_) x id ≡ x)
    repeatₗ-by-1 {_▫_} {x}{id} ⦃ identᵣ ⦄ = identityᵣ(_▫_)(id)

    -- repeatᵣ-by-sum : ∀{_▫_ : X → X → X}{x id} → ⦃ _ : Identityᵣ(_▫_)(id) ⦄ → ∀{a b} → ((repeatᵣ a (_▫_) x id) ▫ (repeatᵣ b (_▫_) x id) ≡ repeatᵣ (a + b) (_▫_) x id)

    repeatₗ-by-sum : ∀{_▫_ : X → X → X}{x id} → ⦃ _ : BinaryOperator(_▫_) ⦄ → ⦃ _ : Identityᵣ(_▫_)(id) ⦄ → ⦃ _ : Associativity(_▫_) ⦄ → ∀{a b} → ((repeatₗ a (_▫_) id x) ▫ (repeatₗ b (_▫_) id x) ≡ repeatₗ (a + b) (_▫_) id x)
    repeatₗ-by-sum {_▫_} {x} {id} ⦃ identᵣ ⦄ {a} {𝟎}   =
      (repeatₗ a (_▫_) id x) ▫ (repeatₗ 𝟎 (_▫_) id x) 🝖-[ reflexivity(_≡_) ]
      (repeatₗ a (_▫_) id x) ▫ id                     🝖-[ identityᵣ(_▫_)(id) ]
      repeatₗ a (_▫_) id x                            🝖-[ reflexivity(_≡_) ]
      repeatₗ (a + 𝟎) (_▫_) id x                      🝖-end
    repeatₗ-by-sum {_▫_} {x} {id} ⦃ identᵣ ⦄ {a} {𝐒 b} =
      (repeatₗ a (_▫_) id x) ▫ (repeatₗ (𝐒(b)) (_▫_) id x)  🝖-[ reflexivity(_≡_) ]
      (repeatₗ a (_▫_) id x) ▫ ((repeatₗ b (_▫_) id x) ▫ x) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
      ((repeatₗ a (_▫_) id x) ▫ (repeatₗ b (_▫_) id x)) ▫ x 🝖-[ [≡]-with2ₗ(_▫_)(_) (repeatₗ-by-sum{a = a}{b = b}) ]
      (repeatₗ (a + b) (_▫_) id x) ▫ x                      🝖-[ reflexivity(_≡_) ]
      repeatₗ (a + 𝐒(b)) (_▫_) id x                         🝖-end

    repeatₗ-by-product : ∀{_▫_ : X → X → X}{x id} → ⦃ _ : BinaryOperator(_▫_) ⦄ → ⦃ _ : Identityᵣ(_▫_)(id) ⦄ → ⦃ _ : Associativity(_▫_) ⦄ → ∀{a b} → (repeatₗ b (_▫_) id ((repeatₗ a (_▫_) id x)) ≡ repeatₗ (a ⋅ b) (_▫_) id x)
    repeatₗ-by-product {_▫_} {x} {id} ⦃ identᵣ ⦄ {a} {𝟎}   =
      repeatₗ 𝟎 (_▫_) id ((repeatₗ a (_▫_) id x)) 🝖-[ reflexivity(_≡_) ]
      repeatₗ (a ⋅ 𝟎) (_▫_) id x                  🝖-end
    repeatₗ-by-product {_▫_} {x} {id} ⦃ identᵣ ⦄ {a} {𝐒 b} =
      repeatₗ (𝐒(b)) (_▫_) id ((repeatₗ a (_▫_) id x))                       🝖-[ reflexivity(_≡_) ]
      (repeatₗ b (_▫_) id ((repeatₗ a (_▫_) id x))) ▫ (repeatₗ a (_▫_) id x) 🝖-[ [≡]-with2ₗ(_▫_)(_) (repeatₗ-by-product{a = a}{b = b}) ]
      (repeatₗ (a ⋅ b) (_▫_) id x) ▫ (repeatₗ a (_▫_) id x)                  🝖-[ repeatₗ-by-sum {a = a ⋅ b}{a} ]
      repeatₗ ((a ⋅ b) + a) (_▫_) id x                                       🝖-[ [≡]-to-equivalence ([≡]-with(expr ↦ repeatₗ expr (_▫_) id x) {a ⋅ b + a}{a + a ⋅ b} (commutativity(_+_) {a ⋅ b})) ]
      repeatₗ (a ⋅ 𝐒(b)) (_▫_) id x                                          🝖-end
      where
        open import Relator.Equals.Proofs.Equivalence using ([≡]-to-equivalence)
