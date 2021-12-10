module Function.Iteration.Proofs where

import Lvl
open import Functional
open import Function.Names as Names using (_⊜_)
open import Function.Iteration
open import Function.Proofs
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper using (_+_ ; _⋅_ ; _𝄩_)
open import Numeral.Natural.Oper.Proofs
open import Relator.Equals renaming (_≡_ to _≡ₑ_)
import      Structure.Function.Names as Names
import      Structure.Function
open import Structure.Operator.Properties
open import Structure.Operator.Proofs.Util
import      Structure.Operator.Names as Names
import      Structure.Operator
open import Structure.Relator.Properties
open import Structure.Function.Domain
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ : Lvl.Level
private variable T A B C X Y Z : Type{ℓ}

module _ where
  open import Structure.Setoid
  open        Structure.Function
  open        Structure.Operator

  module _ ⦃ equiv-X : Equiv{ℓₑ}(X) ⦄ where
    -- Propositions that state something about arbitrary composed functions also apply to arbitrary function iterations of the first function.
    [^]-from-[∘]-proof : ∀{ℓ₂}{P : (X → X) → Type{ℓ₂}} → (∀{f g : X → X} → P(f ∘ g)) → (∀{f : X → X}{n} → P(f ^ n))
    [^]-from-[∘]-proof {P = P} p {f} {𝟎}   = p{id}{id}
    [^]-from-[∘]-proof {P = P} p {f} {𝐒 n} = p{f}{f ^ n}

    [^]-function-raw : ∀{f : X → X} → Names.Congruence₁(f) → ∀{n} → Names.Congruence₁(f ^ n)
    [^]-function-raw func-f {𝟎}    xy = xy
    [^]-function-raw func-f {𝐒(n)} xy = func-f([^]-function-raw func-f {n} xy)

    -- Iterated function is a function when the function is.
    [^]-function : ∀{f : X → X} → ⦃ func : Function(f) ⦄ → ∀{n} → Function(f ^ n)
    Function.congruence ([^]-function ⦃ intro func-f ⦄ {n}) = [^]-function-raw func-f {n}

    [^]-injective-raw : ∀{f : X → X} → Names.Injective(f) → ∀{n} → Names.Injective(f ^ n)
    [^]-injective-raw inj-f {𝟎}    fnxfny = fnxfny
    [^]-injective-raw inj-f {𝐒(n)} fnxfny = [^]-injective-raw inj-f {n} (inj-f fnxfny)

    -- Iterated function is injective when the function is.
    [^]-injective : ∀{f : X → X} → ⦃ inj : Injective(f) ⦄ → ∀{n} → Injective(f ^ n)
    Injective.proof ([^]-injective ⦃ intro inj-f ⦄ {n}) = [^]-injective-raw inj-f {n}

    [^]-surjective-raw : ∀{f : X → X} → ⦃ func : Function(f) ⦄ → Names.Surjective(f) → ∀{n} → Names.Surjective(f ^ n)
    [^]-surjective-raw     surj-f {𝟎}    {y} = [∃]-intro y ⦃ reflexivity(_≡_) ⦄
    [^]-surjective-raw {f} surj-f {𝐒(n)} {y} = [∃]-map-proof (p ↦ (congruence₁(f) p) 🝖 [∃]-proof(surj-f {y})) ([^]-surjective-raw surj-f {n} {[∃]-witness(surj-f {y})})

    -- Iterated function is surjective when the function is.
    [^]-surjective : ∀{f : X → X} → ⦃ func : Function(f) ⦄ → ⦃ surj : Surjective(f) ⦄ → ∀{n} → Surjective(f ^ n)
    Surjective.proof ([^]-surjective ⦃ _ ⦄ ⦃ intro surj-f ⦄ {n}) = [^]-surjective-raw surj-f {n}

    -- Argument applied to the iterated function is one extra iteration.
    -- Note: This implies: (f ^ n)(f x) ≡ f((f ^ n)(x))
    [^]-inner-value : ∀{f : X → X} → ⦃ func : Function(f) ⦄ → ∀{x}{n} → ((f ^ n)(f x) ≡ (f ^ (𝐒(n)))(x))
    [^]-inner-value {f} {x} {𝟎}   = reflexivity(_≡_)
    [^]-inner-value {f} {x} {𝐒 n} = congruence₁(f) ([^]-inner-value {f} {x} {n})

    -- A fixpoint of the function is also a fixpoint of the iterated function.
    [^]-of-fixpoint : ∀{f : X → X} → ⦃ func : Function(f) ⦄ → ∀{x : X} → ⦃ fix : Fixpoint f(x) ⦄ → ∀{n} → ((f ^ n)(x) ≡ x)
    [^]-of-fixpoint {f} {x} {𝟎}    = reflexivity(_≡_)
    [^]-of-fixpoint {f} {x} {𝐒(n)} =
      (f ^ 𝐒(n))(x)    🝖-[ reflexivity(_≡_) ]
      (f ∘ (f ^ n))(x) 🝖-[ reflexivity(_≡_) ]
      f((f ^ n)(x))    🝖-[ congruence₁(f) ([^]-of-fixpoint {f} {x} {n}) ]
      f(x)             🝖-[ fixpoint f(x) ]
      x                🝖-end

  module _ ⦃ equiv-XX : Equiv{ℓₑ}(X → X) ⦄ where
    [^]-by-1 : ∀{f : X → X} → (f ^ 1 ≡ f)
    [^]-by-1 {f} = reflexivity(_≡_)

    [^]-of-id : ∀{n} → (id ^ n ≡ id)
    [^]-of-id {𝟎}   = reflexivity(_≡_)
    [^]-of-id {𝐒 n} = [^]-of-id {n}

    [^]-inner : ∀{f : X → X} → ⦃ _ : Function(f ∘_) ⦄ → ∀{n} → ((f ^ n) ∘ f ≡ f ^ (𝐒(n)))
    [^]-inner {f} {𝟎}   = reflexivity(_≡_)
    [^]-inner {f} {𝐒 n} = congruence₁(f ∘_) ([^]-inner {f} {n})

    [^]-add : ⦃ [∘]-op : BinaryOperator(_∘_) ⦄ → ∀{f : X → X} → ∀{a b} → ((f ^ a) ∘ (f ^ b) ≡ f ^ (a + b))
    [^]-add {f} {𝟎} {𝟎}     = reflexivity(_≡_)
    [^]-add {f} {𝟎} {𝐒 b}   = reflexivity(_≡_)
    [^]-add {f} {𝐒 a} {𝟎}   = reflexivity(_≡_)
    [^]-add ⦃ [∘]-op ⦄ {f} {𝐒 a} {𝐒 b} =
      (f ^ 𝐒(a)) ∘ (f ^ 𝐒(b))    🝖-[ reflexivity(_≡_) ]
      (f ^ 𝐒(a)) ∘ (f ∘ (f ^ b)) 🝖-[ reflexivity(_≡_) ]
      ((f ^ 𝐒(a)) ∘ f) ∘ (f ^ b) 🝖-[ congruence₂-₁(_∘_)(f ^ b) ([^]-inner {f} ⦃ BinaryOperator-unary₂(_∘_){f} ⦄ {𝐒(a)}) ]
      f ∘ ((f ^ 𝐒(a)) ∘ (f ^ b)) 🝖-[ reflexivity(_≡_) ]
      (f ∘ (f ^ 𝐒(a))) ∘ (f ^ b) 🝖-[ congruence₂-₂(_∘_)(f) ([^]-add{f} {𝐒 a} {b}) ]
      f ∘ (f ^ (𝐒(a) + b))       🝖-[ reflexivity(_≡_) ]
      f ^ (𝐒(a) + 𝐒(b))          🝖-end

    [^]-multiply : ⦃ [∘]-op : BinaryOperator(_∘_) ⦄ → ∀{f : X → X} → ∀{a b} → ((f ^ a) ^ b ≡ f ^ (a ⋅ b))
    [^]-multiply ⦃ [∘]-op ⦄ {f} {𝟎}   {𝟎}   = reflexivity(_≡_)
    [^]-multiply ⦃ [∘]-op ⦄ {f} {𝟎}   {𝐒 b} = [^]-of-id {𝐒 b}
    [^]-multiply ⦃ [∘]-op ⦄ {f} {𝐒 a} {𝟎}   = reflexivity(_≡_)
    [^]-multiply ⦃ [∘]-op ⦄ {f} {𝐒 a} {𝐒 b} =
      (f ^ 𝐒(a)) ^ 𝐒(b)             🝖-[ reflexivity(_≡_) ]
      (f ^ 𝐒(a)) ∘ ((f ^ 𝐒(a)) ^ b) 🝖-[ congruence₂-₂(_∘_)(f ^ 𝐒(a)) ([^]-multiply{f} {𝐒 a} {b}) ]
      (f ^ 𝐒(a)) ∘ (f ^ (𝐒(a) ⋅ b)) 🝖-[ [^]-add {f} {𝐒(a)} {𝐒(a) ⋅ b} ]
      f ^ (𝐒(a) + (𝐒(a) ⋅ b))       🝖-[ reflexivity(_≡_) ]
      f ^ (𝐒(a) ⋅ 𝐒(b))             🝖-end

    [^]-distanceₗ : ⦃ [∘]-op : BinaryOperator(_∘_) ⦄ → ∀{f : X → X}{a b} → (f ^ a ≡ f ^ b) ← (f ^ (a 𝄩 b) ≡ id)
    [^]-distanceₗ {f} {𝟎}   {𝟎}   = id
    [^]-distanceₗ {f} {𝟎}   {𝐒 b} = symmetry(_≡_)
    [^]-distanceₗ {f} {𝐒 a} {𝟎}   = id
    [^]-distanceₗ {f} {𝐒 a} {𝐒 b} = congruence₂-₂(_∘_)(f) ∘ ([^]-distanceₗ {f} {a} {b})

    [^]-distanceᵣ : ⦃ [∘]-op : BinaryOperator(_∘_) ⦄ → ⦃ [∘]-cancₗ : Cancellationₗ(_∘_) ⦄ → ∀{f : X → X}{a b} → (f ^ a ≡ f ^ b) → (f ^ (a 𝄩 b) ≡ id)
    [^]-distanceᵣ {f} {𝟎}   {𝟎}   = id
    [^]-distanceᵣ {f} {𝟎}   {𝐒 b} = symmetry(_≡_)
    [^]-distanceᵣ {f} {𝐒 a} {𝟎}   = id
    [^]-distanceᵣ {f} {𝐒 a} {𝐒 b} p = [^]-distanceᵣ {f} {a} {b} (cancellationₗ(_∘_) {f} p)

    module _ ⦃ op : BinaryOperator(_∘_) ⦄ ⦃ assoc : Associativity(_∘_) ⦄ where
      [^]-commuting : ∀{f g : X → X} → Names.Commuting(_∘_)(f)(g) → ∀{a b} → Names.Commuting(_∘_)(f ^ a)(g ^ b)
      [^]-commuting {f} {g} com {𝟎}   {𝟎}   = reflexivity(_≡_)
      [^]-commuting {f} {g} com {𝟎}   {𝐒 b} = reflexivity(_≡_)
      [^]-commuting {f} {g} com {𝐒 a} {𝟎}   = reflexivity(_≡_)
      [^]-commuting {f} {g} com {𝐒 a} {𝐒 b} =
        (f ^ 𝐒(a)) ∘ (g ^ 𝐒(b))       🝖-[ reflexivity(_≡_) ]
        (f ∘ (f ^ a)) ∘ (g ∘ (g ^ b)) 🝖-[ One.associate-commute4 {a = f} {f ^ a} {g} {g ^ b} ([^]-commuting {f} {g} com {a} {1}) ]
        (f ∘ g) ∘ ((f ^ a) ∘ (g ^ b)) 🝖-[ congruence₂(_∘_) com ([^]-commuting {f} {g} com {a} {b}) ]
        (g ∘ f) ∘ ((g ^ b) ∘ (f ^ a)) 🝖-[ One.associate-commute4 {a = g} {f} {g ^ b} {f ^ a} ([^]-commuting {f} {g} com {1} {b}) ]
        (g ∘ (g ^ b)) ∘ (f ∘ (f ^ a)) 🝖-[ reflexivity(_≡_) ]
        (g ^ 𝐒(b)) ∘ (f ^ 𝐒(a))       🝖-end

      [^]-of-[∘] :  ∀{f : X → X}{g : X → X} → Names.Commuting(_∘_)(f)(g) → ∀{n} → ((f ∘ g) ^ n ≡ (f ^ n) ∘ (g ^ n))
      [^]-of-[∘] {f}{g} com {𝟎}   = reflexivity(_≡_)
      [^]-of-[∘] {f}{g} com {𝐒 n} =
        (f ∘ g) ^ 𝐒(n)                🝖-[ reflexivity(_≡_) ]
        (f ∘ g) ∘ ((f ∘ g) ^ n)       🝖-[ congruence₂-₂(_∘_)(f ∘ g) ([^]-of-[∘] {f}{g} com {n}) ]
        (f ∘ g) ∘ ((f ^ n) ∘ (g ^ n)) 🝖-[ One.associate-commute4 {a = f} {g} {f ^ n}{g ^ n} (symmetry(_≡_) ([^]-commuting {f} {g} com {n} {1})) ]
        (f ∘ (f ^ n)) ∘ (g ∘ (g ^ n)) 🝖-[ reflexivity(_≡_) ]
        (f ^ 𝐒(n)) ∘ (g ^ 𝐒(n))       🝖-end

  module _ {ℓ₁}{ℓ₂} {X : Type{ℓ₁}} ⦃ equiv-x : Equiv{ℓₑ₁}(X) ⦄ {Y : Type{ℓ₂}} ⦃ equiv-y : Equiv{ℓₑ₂}(Y) ⦄ where
    private variable n : ℕ
    private variable x : X
    private variable init : Y

    repeatᵣₗ-flip-equality : ∀{_▫_ : Y → X → Y} → ⦃ op : BinaryOperator(_▫_) ⦄ → (repeatᵣ n (swap(_▫_)) x init ≡ repeatₗ n (_▫_) init x)
    repeatᵣₗ-flip-equality {n = 𝟎}                      = reflexivity(_≡_)
    repeatᵣₗ-flip-equality {n = 𝐒(n)}{x = x}{_▫_ = _▫_} = congruence₂-₁(_▫_)(x) (repeatᵣₗ-flip-equality {n = n}{_▫_ = _▫_})

    repeatₗᵣ-flip-equality : ∀{_▫_ : X → Y → Y} → ⦃ op : BinaryOperator(_▫_) ⦄ → (repeatₗ n (swap _▫_) init x ≡ repeatᵣ n (_▫_) x init)
    repeatₗᵣ-flip-equality {n = n}{init = init}{x = x}{_▫_ = _▫_} = symmetry(_≡_) (repeatᵣₗ-flip-equality {n = n}{x = x}{init = init}{_▫_ = swap(_▫_)} ⦃ op = swap-binaryOperator ⦄)

  module _ ⦃ equiv-X : Equiv{ℓₑ}(X) ⦄ where
    private variable f : X → X
    private variable _▫_ : X → X → X
    private variable x elem init : X
    private variable n : ℕ

    [^]-from-repeatᵣ-alt : ⦃ func : Function(f) ⦄ → ((f ^ n) ⊜ repeatᵣ(n) (f ∘_) id)
    [^]-from-repeatᵣ-alt    {n = 𝟎}   = reflexivity(_≡_)
    [^]-from-repeatᵣ-alt {f}{n = 𝐒 n} = congruence₁(f) ([^]-from-repeatᵣ-alt {n = n})

    [^]-from-repeatᵣ : ⦃ func : Function(f) ⦄ → ((f ^ n) ⊜ repeatᵣ(n) (_∘_) f id)
    [^]-from-repeatᵣ    {n = 𝟎}   = reflexivity(_≡_)
    [^]-from-repeatᵣ {f}{n = 𝐒 n} = congruence₁(f) ([^]-from-repeatᵣ {f}{n = n})

    -- TODO: Should also be provable using associativity? Prove (CommutingOn(_▫_)(x)(x) → AssociativityOn(_▫_)(x)). Is this helping?
    repeat-swap-side : ⦃ op : BinaryOperator(_▫_) ⦄ ⦃ comm : Commutativity(_▫_) ⦄ → (repeatₗ n (_▫_) x x ≡ repeatᵣ n (_▫_) x x)
    repeat-swap-side            {n = 𝟎}      = reflexivity(_≡_)
    repeat-swap-side {_▫_ = _▫_}{n = 𝐒 n}{x} = congruence₂-₁(_▫_)(x) (repeat-swap-side {n = n}) 🝖 commutativity(_▫_)

    repeat-swap-side-by-associativity : ⦃ op : BinaryOperator(_▫_) ⦄ ⦃ _ : Associativity(_▫_) ⦄ → (repeatₗ n (_▫_) x x ≡ repeatᵣ n (_▫_) x x)
    repeat-swap-side-by-associativity             {n = 𝟎}         = reflexivity(_≡_)
    repeat-swap-side-by-associativity             {n = 𝐒 𝟎}   {x} = reflexivity(_≡_)
    repeat-swap-side-by-associativity {_▫_ = _▫_} {n = 𝐒(𝐒 n)}{x} =
      repeatₗ (𝐒(𝐒(n))) (_▫_) x x        🝖[ _≡_ ]-[]
      repeatₗ (𝐒(n)) (_▫_) x x ▫ x       🝖[ _≡_ ]-[ congruence₂-₁(_▫_)(x) (repeat-swap-side-by-associativity {n = 𝐒 n}) ]
      repeatᵣ (𝐒(n)) (_▫_) x x ▫ x       🝖[ _≡_ ]-[]
      (x ▫ repeatᵣ n (_▫_) x x) ▫ x      🝖[ _≡_ ]-[ associativity(_▫_) ]
      x ▫ (repeatᵣ n (_▫_) x x ▫ x)      🝖[ _≡_ ]-[ congruence₂-₂(_▫_)(x) (congruence₂-₁(_▫_)(x) (repeat-swap-side-by-associativity {n = n})) ]-sym
      x ▫ (repeatₗ n (_▫_) x x ▫ x)      🝖[ _≡_ ]-[]
      x ▫ repeatₗ (𝐒(n)) (_▫_) x x       🝖[ _≡_ ]-[ congruence₂-₂(_▫_)(x) (repeat-swap-side-by-associativity {n = 𝐒(n)}) ]
      x ▫ repeatᵣ (𝐒(n)) (_▫_) x x       🝖[ _≡_ ]-[]
      repeatᵣ (𝐒(𝐒(n))) (_▫_) x x        🝖[ _≡_ ]-end

    repeat-with-id-swap-side : ⦃ op : BinaryOperator(_▫_) ⦄ ⦃ comm : Commutativity(_▫_) ⦄ ⦃ ident : Identity(_▫_)(init) ⦄ → (repeatₗ n (_▫_) init x ≡ repeatᵣ n (_▫_) x init)
    repeat-with-id-swap-side {n = 𝟎} = reflexivity(_≡_)
    repeat-with-id-swap-side {_▫_ = _▫_}{n = 𝐒 n}{x = x} = congruence₂-₁(_▫_)(x) (repeat-with-id-swap-side {n = n}) 🝖 commutativity(_▫_)

    repeat-raise-equality : ⦃ op : BinaryOperator(_▫_) ⦄ → (repeatᵣ n (_▫_) elem (x) ≡ ((elem ▫_) ^ n)(x))
    repeat-raise-equality           {n = 𝟎}             = reflexivity(_≡_)
    repeat-raise-equality{_▫_ = _▫_}{n = 𝐒(n)}{elem}{x} = congruence₂-₂(_▫_)(elem) (repeat-raise-equality{_▫_ = _▫_}{n = n}{elem}{x})


module _ {X : Type{ℓ}} where
  open import Relator.Equals
  open import Relator.Equals.Proofs

  raise-repeat-equality : ∀{n : ℕ}{f : X → X} → (f ^ n ≡ repeatᵣ n (_∘_) f id)
  raise-repeat-equality{𝟎}       = reflexivity(_≡_)
  raise-repeat-equality{𝐒(n)}{f} = [≡]-with(f ∘_) (raise-repeat-equality{n}{f})

module _ where
  open import Structure.Setoid
  open        Structure.Function
  open        Structure.Operator

  module _ ⦃ equiv-X : Equiv{ℓₑ}(X) ⦄ where
    repeatₗ-by-0 : ∀{_▫_ : X → X → X}{x id} → ⦃ _ : Identityᵣ(_▫_)(id) ⦄ → (repeatᵣ 0 (_▫_) x id ≡ id)
    repeatₗ-by-0 {_▫_} {x}{id} ⦃ identᵣ ⦄ = reflexivity(_≡_)

    repeatₗ-by-1 : ∀{_▫_ : X → X → X}{x id} → ⦃ _ : Identityᵣ(_▫_)(id) ⦄ → (repeatᵣ 1 (_▫_) x id ≡ x)
    repeatₗ-by-1 {_▫_} {x}{id} ⦃ identᵣ ⦄ = identityᵣ(_▫_)(id)

    repeatₗ-by-sum : ∀{_▫_ : X → X → X}{x id} → ⦃ _ : BinaryOperator(_▫_) ⦄ → ⦃ _ : Identityᵣ(_▫_)(id) ⦄ → ⦃ _ : Associativity(_▫_) ⦄ → ∀{a b} → ((repeatₗ a (_▫_) id x) ▫ (repeatₗ b (_▫_) id x) ≡ repeatₗ (a + b) (_▫_) id x)
    repeatₗ-by-sum {_▫_} {x} {id} ⦃ identᵣ ⦄ {a} {𝟎}   =
      (repeatₗ a (_▫_) id x) ▫ (repeatₗ 𝟎 (_▫_) id x) 🝖-[ reflexivity(_≡_) ]
      (repeatₗ a (_▫_) id x) ▫ id                     🝖-[ identityᵣ(_▫_)(id) ]
      repeatₗ a (_▫_) id x                            🝖-[ reflexivity(_≡_) ]
      repeatₗ (a + 𝟎) (_▫_) id x                      🝖-end
    repeatₗ-by-sum {_▫_} {x} {id} ⦃ identᵣ ⦄ {a} {𝐒 b} =
      (repeatₗ a (_▫_) id x) ▫ (repeatₗ (𝐒(b)) (_▫_) id x)  🝖-[ reflexivity(_≡_) ]
      (repeatₗ a (_▫_) id x) ▫ ((repeatₗ b (_▫_) id x) ▫ x) 🝖-[ symmetry(_≡_) (associativity(_▫_)) ]
      ((repeatₗ a (_▫_) id x) ▫ (repeatₗ b (_▫_) id x)) ▫ x 🝖-[ congruence₂-₁(_▫_)(_) (repeatₗ-by-sum{a = a}{b = b}) ]
      (repeatₗ (a + b) (_▫_) id x) ▫ x                      🝖-[ reflexivity(_≡_) ]
      repeatₗ (a + 𝐒(b)) (_▫_) id x                         🝖-end

    repeatₗ-by-product : ∀{_▫_ : X → X → X}{x id} → ⦃ _ : BinaryOperator(_▫_) ⦄ → ⦃ _ : Identityᵣ(_▫_)(id) ⦄ → ⦃ _ : Associativity(_▫_) ⦄ → ∀{a b} → (repeatₗ b (_▫_) id ((repeatₗ a (_▫_) id x)) ≡ repeatₗ (a ⋅ b) (_▫_) id x)
    repeatₗ-by-product {_▫_} {x} {id} ⦃ identᵣ ⦄ {a} {𝟎}   =
      repeatₗ 𝟎 (_▫_) id ((repeatₗ a (_▫_) id x)) 🝖-[ reflexivity(_≡_) ]
      repeatₗ (a ⋅ 𝟎) (_▫_) id x                  🝖-end
    repeatₗ-by-product {_▫_} {x} {id} ⦃ identᵣ ⦄ {a} {𝐒 b} =
      repeatₗ (𝐒(b)) (_▫_) id ((repeatₗ a (_▫_) id x))                       🝖-[ reflexivity(_≡_) ]
      (repeatₗ b (_▫_) id ((repeatₗ a (_▫_) id x))) ▫ (repeatₗ a (_▫_) id x) 🝖-[ congruence₂-₁(_▫_)(_) (repeatₗ-by-product{a = a}{b = b}) ]
      (repeatₗ (a ⋅ b) (_▫_) id x) ▫ (repeatₗ a (_▫_) id x)                  🝖-[ repeatₗ-by-sum {a = a ⋅ b}{a} ]
      repeatₗ ((a ⋅ b) + a) (_▫_) id x                                       🝖-[ [≡]-to-equivalence (congruence₁(expr ↦ repeatₗ expr (_▫_) id x) {a ⋅ b + a}{a + a ⋅ b} (commutativity(_+_) {a ⋅ b})) ]
      repeatₗ (a ⋅ 𝐒(b)) (_▫_) id x                                          🝖-end
      where
        open import Relator.Equals.Proofs.Equiv using ([≡]-to-equivalence)

    repeatₗ-by-distanceₗ : ∀{_▫_ : X → X → X}{x id} → ⦃ _ : BinaryOperator(_▫_) ⦄ → ⦃ _ : Identityᵣ(_▫_)(id) ⦄ → ⦃ _ : Associativity(_▫_) ⦄ → ∀{a b} → (repeatₗ a (_▫_) id x ≡ repeatₗ b (_▫_) id x) ← (repeatₗ (a 𝄩 b) (_▫_) id x ≡ id)
    repeatₗ-by-distanceₗ {_▫_} {x} {id} {𝟎}   {𝟎}   p = p
    repeatₗ-by-distanceₗ {_▫_} {x} {id} {𝟎}   {𝐒 b} p = symmetry(_≡_) p
    repeatₗ-by-distanceₗ {_▫_} {x} {id} {𝐒 a} {𝟎}   p = p
    repeatₗ-by-distanceₗ {_▫_} {x} {id} {𝐒 a} {𝐒 b} p = congruence₂-₁(_▫_)(_) (repeatₗ-by-distanceₗ {_▫_} {x} {id} {a} {b} p)

    repeatₗ-by-distanceᵣ : ∀{_▫_ : X → X → X}{x id} → ⦃ _ : BinaryOperator(_▫_) ⦄ → ⦃ _ : Identityᵣ(_▫_)(id) ⦄ → ⦃ _ : Associativity(_▫_) ⦄ → ⦃ cancᵣ : Cancellationᵣ(_▫_) ⦄ → ∀{a b} → (repeatₗ a (_▫_) id x ≡ repeatₗ b (_▫_) id x) → (repeatₗ (a 𝄩 b) (_▫_) id x ≡ id)
    repeatₗ-by-distanceᵣ {_▫_} {x} {id} {𝟎}   {𝟎}   p = p
    repeatₗ-by-distanceᵣ {_▫_} {x} {id} {𝟎}   {𝐒 b} p = symmetry(_≡_) p
    repeatₗ-by-distanceᵣ {_▫_} {x} {id} {𝐒 a} {𝟎}   p = p
    repeatₗ-by-distanceᵣ {_▫_} {x} {id} {𝐒 a} {𝐒 b} p = repeatₗ-by-distanceᵣ {_▫_} {x} {id} {a} {b} (cancellationᵣ(_▫_) {x} p)

    module _ {_▫₁_ _▫₂_ : X → X → X}{id} ⦃ op₂ : BinaryOperator(_▫₂_) ⦄ ⦃ distₗ : Distributivityₗ(_▫₁_)(_▫₂_) ⦄ ⦃ absᵣ : Absorberᵣ(_▫₁_)(id) ⦄ where
      repeatₗ-distributivityₗ : ∀{x y}{n} → (x ▫₁ (repeatₗ n (_▫₂_) id y) ≡ repeatₗ n (_▫₂_) id (x ▫₁ y))
      repeatₗ-distributivityₗ       {n = 𝟎}    = absorberᵣ(_▫₁_)(id)
      repeatₗ-distributivityₗ {x}{y}{n = 𝐒(n)} =
        x ▫₁ (repeatₗ(𝐒(n)) (_▫₂_) id y)           🝖[ _≡_ ]-[]
        x ▫₁ ((repeatₗ n (_▫₂_) id y) ▫₂ y)        🝖[ _≡_ ]-[ distributivityₗ(_▫₁_)(_▫₂_) ]
        (x ▫₁ (repeatₗ n (_▫₂_) id y)) ▫₂ (x ▫₁ y) 🝖[ _≡_ ]-[ congruence₂-₁(_▫₂_)(x ▫₁ y) (repeatₗ-distributivityₗ {x}{y}{n = n}) ]
        (repeatₗ n (_▫₂_) id (x ▫₁ y)) ▫₂ (x ▫₁ y) 🝖[ _≡_ ]-[]
        repeatₗ(𝐒(n)) (_▫₂_) id (x ▫₁ y)           🝖-end

    module _ {_▫₁_ _▫₂_ : X → X → X}{id} ⦃ op₂ : BinaryOperator(_▫₂_) ⦄ ⦃ distₗ : Distributivityᵣ(_▫₁_)(_▫₂_) ⦄ ⦃ absₗ : Absorberₗ(_▫₁_)(id) ⦄ where
      repeatₗ-distributivityᵣ : ∀{x y}{n} → ((repeatₗ n (_▫₂_) id x) ▫₁ y ≡ repeatₗ n (_▫₂_) id (x ▫₁ y))
      repeatₗ-distributivityᵣ       {n = 𝟎}    = absorberₗ(_▫₁_)(id)
      repeatₗ-distributivityᵣ {x}{y}{n = 𝐒(n)} =
        (repeatₗ(𝐒(n)) (_▫₂_) id x) ▫₁ y           🝖[ _≡_ ]-[]
        ((repeatₗ n (_▫₂_) id x) ▫₂ x) ▫₁ y        🝖[ _≡_ ]-[ distributivityᵣ(_▫₁_)(_▫₂_) ]
        ((repeatₗ n (_▫₂_) id x) ▫₁ y) ▫₂ (x ▫₁ y) 🝖[ _≡_ ]-[ congruence₂-₁(_▫₂_)(x ▫₁ y) (repeatₗ-distributivityᵣ {x}{y}{n = n}) ]
        (repeatₗ n (_▫₂_) id (x ▫₁ y)) ▫₂ (x ▫₁ y) 🝖[ _≡_ ]-[]
        repeatₗ(𝐒(n)) (_▫₂_) id (x ▫₁ y)           🝖-end

    module _ {_▫₁_ _▫₂_ : X → X → X} ⦃ op₂ : BinaryOperator(_▫₂_) ⦄ {id₁ id₂}{x₁ x₂} where
      repeatₗ-function : ∀{n₁ n₂} → (n₁ ≡ₑ n₂) → (∀{x y} → (x ▫₁ y ≡ x ▫₂ y)) → (id₁ ≡ id₂) → (x₁ ≡ x₂) → (repeatₗ n₁ (_▫₁_) id₁ x₁ ≡ repeatₗ n₂ (_▫₂_) id₂ x₂)
      repeatₗ-function {n₁ = 𝟎}   [≡]-intro eq-op eq-id eq-x = eq-id
      repeatₗ-function {n₁ = 𝐒 n} [≡]-intro eq-op eq-id eq-x =
        repeatₗ (𝐒 n) (_▫₁_) id₁ x₁     🝖[ _≡_ ]-[]
        (repeatₗ n (_▫₁_) id₁ x₁) ▫₁ x₁ 🝖[ _≡_ ]-[ eq-op ]
        (repeatₗ n (_▫₁_) id₁ x₁) ▫₂ x₁ 🝖[ _≡_ ]-[ congruence₂(_▫₂_) (repeatₗ-function {n₁ = n} [≡]-intro eq-op eq-id eq-x) eq-x ]
        (repeatₗ n (_▫₂_) id₂ x₂) ▫₂ x₂ 🝖[ _≡_ ]-[]
        repeatₗ (𝐒 n) (_▫₂_) id₂ x₂     🝖-end
