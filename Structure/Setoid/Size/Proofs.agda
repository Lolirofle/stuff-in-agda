module Structure.Setoid.Size.Proofs where

open import Data
open import Data.Proofs
import      Data.Either        as Either
import      Data.Either.Proofs.Map as Either
import      Lvl
open import Functional
open import Function.Domains
open import Function.Inverseₗ
open import Function.Inverse
open import Function.Iteration
open import Function.Proofs
open import Functional.Instance
open import Logic
open import Logic.Classical
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Setoid.Size
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Function
open import Structure.Relator.Equivalence
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type.Properties.Inhabited
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₗ : Lvl.Level
private variable A B C : Setoid{ℓₑ}{ℓ}
private variable X Y Z : Type{ℓ}

module _ where
  instance
    [≍]-to-[≼] : (_≍_ {ℓₑ₁}{ℓ₁}{ℓₑ₂}{ℓ₂}) ⊆₂ (_≼_)
    _⊆₂_.proof [≍]-to-[≼] ([∃]-intro(f) ⦃ [∧]-intro f-function f-bijective ⦄) =
      ([∃]-intro(f) ⦃ [∧]-intro f-function (bijective-to-injective(f) ⦃ f-bijective ⦄) ⦄)

  instance
    [≍]-to-[≽] : (_≍_ {ℓₑ₁}{ℓ₁}{ℓₑ₂}{ℓ₂}) ⊆₂ (_≽_)
    _⊆₂_.proof [≍]-to-[≽] ([∃]-intro(f) ⦃ [∧]-intro f-function f-bijective ⦄) =
      ([∃]-intro(f) ⦃ [∧]-intro f-function (bijective-to-surjective(f) ⦃ f-bijective ⦄) ⦄)

  [≼]-empty-is-minimal : (([∃]-intro(Empty{ℓ})) ≼ A)
  [≼]-empty-is-minimal = [∃]-intro empty ⦃ [∧]-intro empty-function empty-injective ⦄

  [≽]-empty-is-not-minimal : ¬(∀{A : Setoid{ℓ}} → (A ≽ ([∃]-intro(Empty{ℓ}))))
  [≽]-empty-is-not-minimal proof with () ← [∃]-witness(proof {[∃]-intro Unit}) <>

  [≼]-to-[≽]-not-all : ¬((_≼_ {ℓ}) ⊆₂ swap(_≽_))
  [≼]-to-[≽]-not-all (intro proof) = [≽]-empty-is-not-minimal(proof [≼]-empty-is-minimal)

  module _ ⦃ classical-fiber-existence : ∀{f : [∃]-witness A → [∃]-witness B}{y} → Classical(∃(Fiber f(y))) ⦄ ⦃ inh-A : (◊([∃]-witness A)) ⦄ where
    [≼]-to-[≽]-for-inhabited : ((A ≼ B) → (B ≽ A))
    [≼]-to-[≽]-for-inhabited ([∃]-intro f ⦃ [∧]-intro f-func f-inj ⦄) = [∃]-intro
      (invₗ-construction(const inhabitant) f)
      ⦃ [∧]-intro (invₗ-construction-function ⦃ inj = f-inj ⦄) (inverseₗ-surjective ⦃ inverₗ = invₗ-construction-inverseₗ ⦃ inj = f-inj ⦄ ⦄) ⦄

  {- TODO: Maybe this proof could be made to a proof about invertibility instead
  [≼][≍]-almost-antisymmetry : ⦃ _ : ∀{ℓ}{P : Stmt{ℓ}} → Classical(P) ⦄ → (A ≼ B) → (B ≼ A) → (A ≽ B)
  [≼][≍]-almost-antisymmetry {A = A}{B = B} ([∃]-intro f ⦃ [∧]-intro func-f inj-f ⦄) ([∃]-intro g ⦃ [∧]-intro func-g inj-g ⦄) = [∃]-intro h ⦃ [∧]-intro func-h surj-h ⦄ where
    h : [∃]-witness A → [∃]-witness B
    h(a) = Either.map1 [∃]-witness (const(f(a))) (excluded-middle(∃(b ↦ g(b) ≡ a)))

    func-h : Function(h)
    Function.congruence func-h {a₁} {a₂} a₁a₂ with excluded-middle(∃(b ↦ g(b) ≡ a₁)) | excluded-middle(∃(b ↦ g(b) ≡ a₂)) | a₁a₂ -- TODO: Not sure why the last a₁a₂ is neccessary for the result to normalize from the cases, if this is a bug in Agda or if it is intended. An alternative is to just use two-layered Either.map1-values
    ... | [∨]-introₗ ([∃]-intro b₁ ⦃ gba1 ⦄) | [∨]-introₗ ([∃]-intro b₂ ⦃ gba2 ⦄) | _ = injective(g) ⦃ inj-g ⦄ (gba1 🝖 a₁a₂ 🝖 symmetry(_≡_) gba2)
    ... | [∨]-introₗ ([∃]-intro b₁ ⦃ gba1 ⦄) | [∨]-introᵣ ngba2                   | _ = [⊥]-elim(ngba2([∃]-intro b₁ ⦃ gba1 🝖 a₁a₂ ⦄))
    ... | [∨]-introᵣ ngba1                   | [∨]-introₗ ([∃]-intro b₂ ⦃ gba2 ⦄) | _ = [⊥]-elim(ngba1([∃]-intro b₂ ⦃ gba2 🝖 symmetry(_≡_) a₁a₂ ⦄))
    ... | [∨]-introᵣ _                       | [∨]-introᵣ _                       | _ = congruence₁(f) ⦃ func-f ⦄ a₁a₂

      {- TODO: This choice of h probably does not work for proving antisymmetry because nothing states that f and g are inverses, which is neccessary for this kind of proof
      inj-h : Injective(h)
      Injective.proof inj-h {a₁} {a₂} ha₁ha₂ with excluded-middle(∃(b ↦ g(b) ≡ a₁)) | excluded-middle(∃(b ↦ g(b) ≡ a₂)) | ha₁ha₂
      ... | [∨]-introₗ ([∃]-intro b₁ ⦃ gba1 ⦄) | [∨]-introₗ ([∃]-intro b₂ ⦃ gba2 ⦄) | b₁b₂ =
        a₁    🝖-[ gba1 ]-sym
        g(b₁) 🝖-[ congruence₁(g) ⦃ func-g ⦄ b₁b₂ ]
        g(b₂) 🝖-[ gba2 ]
        a₂    🝖-end
      ... | [∨]-introₗ ([∃]-intro b₁ ⦃ gba1 ⦄) | [∨]-introᵣ nega₂                   | b₁fa₂ = [⊥]-elim(nega₂ ([∃]-intro (f(a₂)) ⦃ p ⦄)) where
        p =
          g(f(a₂)) 🝖-[ congruence₁(g) ⦃ func-g ⦄ b₁fa₂ ]-sym
          g(b₁)    🝖-[ gba1 ]
          a₁       🝖-[ {!gba1!} ]
          a₂       🝖-end
        q =
          f(a₁)    🝖-[ congruence₁(f) ⦃ func-f ⦄ gba1 ]-sym
          f(g(b₁)) 🝖-[ {!!} ]
          b₁       🝖-[ b₁fa₂ ]
          f(a₂)    🝖-end
      ... | [∨]-introᵣ nega₁                   | [∨]-introₗ ([∃]-intro b₂ ⦃ gba2 ⦄) | fa₁b₂ = {!!}
      ... | [∨]-introᵣ nega₁                   | [∨]-introᵣ nega₂                   | fa₁fa₂ = injective(f) ⦃ inj-f ⦄ fa₁fa₂
      -}

    -- TODO: Is it possible to use [≼]-to-[≽]-for-inhabited instead or maybe this should be moved out?
    surj-h : Surjective(h)
    Surjective.proof surj-h {b} with Either.map1-values{f = [∃]-witness}{g = const(f(g(b)))}{e = excluded-middle(∃(x ↦ g(x) ≡ g(b)))}
    ... | [∨]-introₗ ([∃]-intro ([∃]-intro b₂ ⦃ gb₂gb ⦄) ⦃ fgbb₂ ⦄) = [∃]-intro (g(b)) ⦃ fgbb₂ 🝖 injective(g) ⦃ inj-g ⦄ gb₂gb ⦄
    ... | [∨]-introᵣ([∃]-intro neggb ⦃ p ⦄) = [⊥]-elim(neggb ([∃]-intro b ⦃ reflexivity(_≡_) ⦄))
  -}

  open import Structure.Operator
  open import Structure.Setoid.Uniqueness
  module _ ⦃ equiv-X : Equiv{ℓₑ₁}(X) ⦄ ⦃ equiv-Y : Equiv{ℓₑ₂}(Y) ⦄ (P : X → Type{ℓₗ}) ⦃ classical-P : Classical(∃ P) ⦄ (c : ¬(∃ P) → Y) (f : X → Y) ⦃ func-f : Function(f) ⦄ where -- TODO: Maybe f should also be able to depend on P, so that (f : (x : X) → P(x) → Y)?
    -- TODO: This is a generalization of both h in [≼][≍]-antisymmetry-raw and invₗ-construction from Function.Inverseₗ
    existence-decider : Y
    existence-decider = Either.map1 (f ∘ [∃]-witness) c (excluded-middle(∃ P))

    existence-decider-satisfaction-value : Unique(P) → ∀{x} → P(x) → (f(x) ≡ existence-decider)
    existence-decider-satisfaction-value unique-P {x} px with Classical.excluded-middle classical-P
    ... | Either.Left  ([∃]-intro y ⦃ py ⦄) = congruence₁(f) (unique-P px py)
    ... | Either.Right nep with () ← nep ([∃]-intro x ⦃ px ⦄)

    existence-decider-unsatisfaction-value : ⦃ Constant(c) ⦄ → (p : ¬(∃ P)) → (c(p) ≡ existence-decider)
    existence-decider-unsatisfaction-value nep with Classical.excluded-middle classical-P
    ... | Either.Left  ep with () ← nep ep
    ... | Either.Right _ = constant(c)

  module _ ⦃ equiv-X : Equiv{ℓₑ₁}(X) ⦄ ⦃ equiv-Y : Equiv{ℓₑ₂}(Y) ⦄ ⦃ equiv-Z : Equiv{ℓₑ₃}(Z) ⦄ (P : X → Y → Type{ℓₗ}) ⦃ classical-P : ∀{x} → Classical(∃(P(x))) ⦄ (c : (x : X) → ¬(∃(P(x))) → Z) (f : X → Y → Z) ⦃ func-f : BinaryOperator(f) ⦄ where
    existence-decider-fn : X → Z
    existence-decider-fn(x) = existence-decider (P(x)) (c(x)) (f(x)) ⦃ BinaryOperator.unary₂ func-f ⦄

    open import Structure.Relator
    existence-decider-fn-function : (∀{x} → Unique(P(x))) → (∀{x₁ x₂}{p₁ p₂} → (x₁ ≡ x₂) → (c x₁ p₁ ≡ c x₂ p₂)) → ⦃ ∀{y} → UnaryRelator(swap P y) ⦄ → Function(existence-decider-fn)
    Function.congruence (existence-decider-fn-function unique constant) {x₁} {x₂} x₁x₂ with excluded-middle(∃(P(x₁))) | excluded-middle(∃(P(x₂))) | x₁x₂
    ... | [∨]-introₗ ([∃]-intro y₁ ⦃ p₁ ⦄) | [∨]-introₗ ([∃]-intro y₂ ⦃ p₂ ⦄) | _
      = congruence₂(f) x₁x₂ (unique (substitute₁ᵣ(swap P y₁) x₁x₂ p₁) p₂)
    ... | [∨]-introₗ ([∃]-intro y₁ ⦃ p₁ ⦄) | [∨]-introᵣ ngba2 | _
      with () ← ngba2 ([∃]-intro y₁ ⦃ substitute₁ᵣ(swap P y₁) x₁x₂ p₁ ⦄)
    ... | [∨]-introᵣ ngba1 | [∨]-introₗ ([∃]-intro y₂ ⦃ p₂ ⦄) | _
      with () ← ngba1 ([∃]-intro y₂ ⦃ substitute₁ᵣ(swap P y₂) (symmetry(_≡_) x₁x₂) p₂ ⦄)
    ... | [∨]-introᵣ _ | [∨]-introᵣ _ | _ = constant x₁x₂

    existence-decider-fn-surjective : (∀{x} → Unique(P(x))) → ⦃ ∀{x} → Constant(c(x)) ⦄ → (∀{z} → ∃(x ↦ (∀{y} → P(x)(y) → (f x y ≡ z)) ∧ ((nepx : ¬ ∃(P(x))) → (c x nepx ≡ z)))) → Surjective(existence-decider-fn)
    Surjective.proof (existence-decider-fn-surjective unique-p property) {z} with [∃]-intro x ⦃ px ⦄ ← property{z} with excluded-middle(∃(P(x)))
    ... | [∨]-introₗ ([∃]-intro y ⦃ pxy ⦄)
      = [∃]-intro x ⦃ symmetry(_≡_) (existence-decider-satisfaction-value(P(x)) (c(x)) (f(x)) ⦃ BinaryOperator.unary₂ func-f ⦄ unique-p pxy) 🝖 [∧]-elimₗ px pxy ⦄
    ... | [∨]-introᵣ nepx
      = [∃]-intro x ⦃ symmetry(_≡_) (existence-decider-unsatisfaction-value(P(x)) (c(x)) (f(x)) ⦃ BinaryOperator.unary₂ func-f ⦄ nepx) 🝖 [∧]-elimᵣ px nepx ⦄

    existence-decider-fn-surjective2 : (∀{x} → Unique(P(x))) → ⦃ ∀{x} → Constant(c(x)) ⦄ → (∃{Obj = Z → X}(x ↦ (∀{z}{y} → P(x(z))(y) → (f (x(z)) y ≡ z)) ∧ (∀{z} → (nepx : ¬ ∃(P(x(z)))) → (c (x(z)) nepx ≡ z)))) → Surjective(existence-decider-fn)
    Surjective.proof (existence-decider-fn-surjective2 unique-p property) {z} with [∃]-intro x ⦃ px ⦄ ← property with excluded-middle(∃(P(x(z))))
    ... | [∨]-introₗ ([∃]-intro y ⦃ pxy ⦄)
      = [∃]-intro (x(z)) ⦃ symmetry(_≡_) (existence-decider-satisfaction-value(P(x(z))) (c(x(z))) (f(x(z))) ⦃ BinaryOperator.unary₂ func-f ⦄ unique-p pxy) 🝖 [∧]-elimₗ px pxy ⦄
    ... | [∨]-introᵣ nepx
      = [∃]-intro (x(z)) ⦃ symmetry(_≡_) (existence-decider-unsatisfaction-value(P(x(z))) (c(x(z))) (f(x(z))) ⦃ BinaryOperator.unary₂ func-f ⦄ nepx) 🝖 [∧]-elimᵣ px nepx ⦄

    module _
      (inj-f   : ∀{x₁ x₂}{y₁ y₂} → P(x₁)(y₁) → P(x₂)(y₂) → (f x₁ y₁ ≡ f x₂ y₂) → (x₁ ≡ x₂))
      (inj-c   : ∀{x₁ x₂} → (nep₁ : ¬ ∃(P(x₁))) → (nep₂ : ¬ ∃(P(x₂))) → (c x₁ nep₁ ≡ c x₂ nep₂) → (x₁ ≡ x₂))
      (inj-mix : ∀{x₁ x₂}{y₁} → P(x₁)(y₁) → (nep₂ : ¬ ∃(P(x₂))) → (f x₁ y₁ ≡ c x₂ nep₂) → (x₁ ≡ x₂))
      where

      existence-decider-fn-injective : Injective(existence-decider-fn)
      Injective.proof existence-decider-fn-injective {x₁}{x₂} dx₁dx₂ with excluded-middle(∃(P(x₁))) | excluded-middle(∃(P(x₂))) | dx₁dx₂
      ... | Either.Left ([∃]-intro y₁ ⦃ p₁ ⦄) | Either.Left ([∃]-intro y₂ ⦃ p₂ ⦄) | fx₁y₁fx₂y₂ = inj-f p₁ p₂ fx₁y₁fx₂y₂
      ... | Either.Left ([∃]-intro y₁ ⦃ p₁ ⦄) | Either.Right nep₂                 | fxy₁cxp₂   = inj-mix p₁ nep₂ fxy₁cxp₂
      ... | Either.Right nep₁                 | Either.Left ([∃]-intro y₂ ⦃ p₂ ⦄) | cxp₁fxy₂   = symmetry(_≡_) (inj-mix p₂ nep₁ (symmetry(_≡_) cxp₁fxy₂))
      ... | Either.Right nep₁                 | Either.Right nep₂                 | cxp₁cxp₂   = inj-c nep₁ nep₂ cxp₁cxp₂

module _ ⦃ classical : ∀{ℓ}{P : Stmt{ℓ}} → Classical(P) ⦄ where
  -- ⦃ classical-fiber-existence-AB : ∀{f : [∃]-witness A → [∃]-witness B}{y} → Classical(∃(Fiber f(y))) ⦄ → ⦃ classical-fiber-existence-BA : ∀{f : [∃]-witness B → [∃]-witness A}{y} → Classical(∃(Fiber f(y))) ⦄
  open import Structure.Operator
  open import Structure.Relator
  open import Structure.Setoid.Uniqueness

  -- The property of antisymmetry for injection existence.
  -- Also called: Cantor-Schröder-Bernstein Theorem, Schröder-Bernstein Theorem, Cantor–Bernstein theorem
  -- Source: https://artofproblemsolving.com/wiki/index.php/Schroeder-Bernstein_Theorem
  [≼][≍]-antisymmetry-raw : (A ≼ B) → (B ≼ A) → (A ≍ B) -- TODO: Not everything needs to be classical, only forall, exists, and equality
  [≼][≍]-antisymmetry-raw {A = [∃]-intro A}{B = [∃]-intro B} ([∃]-intro f ⦃ [∧]-intro func-f inj-f ⦄) ([∃]-intro g ⦃ [∧]-intro func-g inj-g ⦄) = [∃]-intro h ⦃ [∧]-intro func-h (injective-surjective-to-bijective(h)) ⦄ where
    open import Logic.Predicate.Theorems
    open import Function.Inverseₗ
    open import Numeral.Natural
    open import Structure.Relator

    -- A lone point `b` of `B` is a point not in the image of `f`.
    Lone : B → Stmt
    Lone(b) = ∀{a} → (f(a) ≢ b)

    -- A point `b₁` is a descendent from a point `b₀` in `B` when a number of compositions of `(f ∘ g)` on `b₀` yields `b₁`.
    Desc : B → B → Stmt
    Desc(b₁)(b₀) = ∃(n ↦ (b₁ ≡ ((f ∘ g) ^ n)(b₀)))

    instance
      lone-desc-rel : ∀{y} → UnaryRelator(x ↦ Lone(y) ∧ Desc(f(x)) y)
      lone-desc-rel = UnaryRelator-introᵣ \xy → [∧]-map id (ep ↦ [∃]-map-proof-dependent ep (symmetry(_≡_) (congruence₁(f) ⦃ func-f ⦄ xy) 🝖_))

    f⁻¹ : B → A
    f⁻¹ = invₗ-construction g f

    g⁻¹ : A → B
    g⁻¹ = invₗ-construction f g

    instance
      func-f⁻¹ : Function(f⁻¹)
      func-f⁻¹ = invₗ-construction-function ⦃ inj = inj-f ⦄ ⦃ func-g ⦄

    instance
      func-g⁻¹ : Function(g⁻¹)
      func-g⁻¹ = invₗ-construction-function ⦃ inj = inj-g ⦄ ⦃ func-f ⦄

    instance
      inverₗ-f⁻¹ : Inverseₗ(f)(f⁻¹)
      inverₗ-f⁻¹ = invₗ-construction-inverseₗ ⦃ inj = inj-f ⦄ ⦃ func-g ⦄

    instance
      inverₗ-g⁻¹ : Inverseₗ(g)(g⁻¹)
      inverₗ-g⁻¹ = invₗ-construction-inverseₗ ⦃ inj = inj-g ⦄ ⦃ func-f ⦄

    instance
      func-const-invₗ-construction : BinaryOperator(const ∘ g⁻¹)
      func-const-invₗ-construction = BinaryOperator-unary-intro _ infer const-function

    -- The to-be-proven bijection.
    -- `h` is a mapping such that:
    -- • If `f(a)` is a descendent of a lonely point,     then `h(a) = g⁻¹(a)`.
    -- • If `f(a)` is not a descendent of a lonely point, then `h(a) = f(a)`.
    -- Note: The construction of this function requires excluded middle.
    h : A → B
    h = existence-decider-fn (a ↦ b ↦ Lone(b) ∧ Desc(f(a))(b)) (\a _ → f(a)) (\a _ → g⁻¹(a))

    -- The left inverse of `g` is a right inverse on a point `a` when `f(a)` is a descendent of a lonely point.
    inverᵣ-g⁻¹-specific : ∀{a}{b} → Lone(b) → Desc(f(a))(b) → (g(g⁻¹(a)) ≡ a)
    inverᵣ-g⁻¹-specific        lone-b ([∃]-intro 𝟎      ⦃ desc-b ⦄) with () ← lone-b desc-b
    inverᵣ-g⁻¹-specific {a}{b} lone-b ([∃]-intro (𝐒(n)) ⦃ desc-b ⦄) =
      g(g⁻¹(a))                   🝖[ _≡_ ]-[ congruence₁(g) ⦃ func-g ⦄ (congruence₁(g⁻¹) (injective(f) ⦃ inj-f ⦄ desc-b)) ]
      g(g⁻¹(g(((f ∘ g) ^ n)(b)))) 🝖[ _≡_ ]-[ congruence₁(g) ⦃ func-g ⦄ (inverseₗ(g)(g⁻¹)) ]
      g(((f ∘ g) ^ n)(b))         🝖[ _≡_ ]-[ inverseₗ(f)(f⁻¹) ]-sym
      f⁻¹(f(g(((f ∘ g) ^ n)(b)))) 🝖[ _≡_ ]-[]
      f⁻¹(((f ∘ g) ^ 𝐒(n))(b))    🝖[ _≡_ ]-[ congruence₁(f⁻¹) desc-b ]-sym
      f⁻¹(f(a))                   🝖[ _≡_ ]-[ inverseₗ(f)(f⁻¹) ]
      a                           🝖-end

    inj-different-fgn : ∀{n₁ n₂}{b₁ b₂} → (((f ∘ g) ^ n₁)(b₁) ≡ ((f ∘ g) ^ n₂)(b₂)) → ∃(n ↦ (b₁ ≡ ((f ∘ g) ^ 𝐒(n))(b₂)) ∨ (((f ∘ g) ^ 𝐒(n))(b₁) ≡ b₂) ∨ (b₁ ≡ b₂))
    inj-different-fgn {𝟎}    {𝟎}    p = [∃]-intro 𝟎 ⦃ [∨]-introᵣ p ⦄
    inj-different-fgn {𝟎}    {𝐒 n₂} p = [∃]-intro n₂ ⦃ [∨]-introₗ([∨]-introₗ p) ⦄
    inj-different-fgn {𝐒 n₁} {𝟎}    p = [∃]-intro n₁ ⦃ [∨]-introₗ([∨]-introᵣ p) ⦄
    inj-different-fgn {𝐒 n₁} {𝐒 n₂} p = inj-different-fgn {n₁} {n₂} (Injective.proof inj-g(Injective.proof inj-f p))

    -- The lonely points are unique for all descendents from the image of `f`.
    unique-lone-descendant : ∀{a} → Unique(b ↦ Lone(b) ∧ Desc(f(a))(b))
    unique-lone-descendant {a} {b₁} {b₂} ([∧]-intro lone-b₁ ([∃]-intro n₁ ⦃ desc-b₁ ⦄)) ([∧]-intro lone-b₂ ([∃]-intro n₂ ⦃ desc-b₂ ⦄)) with inj-different-fgn{n₁}{n₂}{b₁}{b₂} (symmetry(_≡_) desc-b₁ 🝖 desc-b₂)
    ... | [∃]-intro n ⦃ Either.Left(Either.Left  p) ⦄ with () ← lone-b₁ (symmetry(_≡_) p)
    ... | [∃]-intro n ⦃ Either.Left(Either.Right p) ⦄ with () ← lone-b₂ p
    ... | [∃]-intro n ⦃ Either.Right b₁b₂ ⦄ = b₁b₂

    instance
      func-h : Function(h)
      func-h = existence-decider-fn-function (a ↦ b ↦ Lone(b) ∧ Desc(f(a))(b)) (\x _ → f(x)) (const ∘ g⁻¹) unique-lone-descendant (congruence₁(f) ⦃ func-f ⦄)

    -- What it means to not have a lonely descendent.
    not-lone-desc : ∀{a} → ¬ ∃(b ↦ Lone(b) ∧ Desc(f(a)) b) → (∀{b} → (∃(x ↦ f(x) ≡ b) ∨ (∀{n} → (f(a) ≢ ((f ∘ g) ^ n)(b)))))
    not-lone-desc {z} = (\nepx {x} → (Either.map ([∃]-map-proof [¬¬]-elim ∘ [¬∀]-to-[∃¬] ⦃ classical ⦄ ⦃ classical ⦄) [¬∃]-to-[∀¬] ∘ [¬]-preserves-[∧][∨]ᵣ) (nepx{x})) ∘ [¬∃]-to-[∀¬]

    instance
      surj-h : Surjective(h)
      Surjective.proof surj-h {z} with excluded-middle(∃(y ↦ Lone(y) ∧ Desc(f(g(z))) y))
      ... | [∨]-introₗ ([∃]-intro y ⦃ pxy ⦄)
        = [∃]-intro (g(z)) ⦃ symmetry(_≡_) (existence-decider-satisfaction-value(y ↦ Lone(y) ∧ Desc(f(g(z))) y) (\_ → f(g(z))) (\_ → g⁻¹(g(z))) unique-lone-descendant pxy) 🝖 inverseₗ(g)(g⁻¹) ⦄
      ... | [∨]-introᵣ nepx
        = [∨]-elim
          (\([∃]-intro x ⦃ p ⦄) → [∃]-intro x ⦃ symmetry(_≡_) (existence-decider-unsatisfaction-value(y ↦ Lone(y) ∧ Desc(f(x)) y) (\_ → f(x)) (\_ → g⁻¹(x)) ⦃ const-function ⦄ ⦃ intro(reflexivity(_≡_)) ⦄ \([∃]-intro xx ⦃ [∧]-intro pp₁ ([∃]-intro n ⦃ pp₂ ⦄) ⦄) → nepx ([∃]-intro xx ⦃ [∧]-intro (\{xxx} ppp → pp₁ ppp) ([∃]-intro (𝐒(n)) ⦃ congruence₁(f) ⦃ func-f ⦄ (congruence₁(g) ⦃ func-g ⦄ (symmetry(_≡_) p 🝖 pp₂)) ⦄) ⦄)) 🝖 p ⦄)
          (\p → [∃]-intro (g(z)) ⦃ symmetry(_≡_) (existence-decider-unsatisfaction-value(y ↦ Lone(y) ∧ Desc(f(g(z))) y) (\_ → f(g(z))) (\_ → g⁻¹(g(z))) ⦃ const-function ⦄ ⦃ intro(reflexivity(_≡_)) ⦄ nepx) 🝖 [⊥]-elim(p{1} (reflexivity(_≡_))) ⦄)
          (not-lone-desc nepx {z})
      {-TODO: How to define surj-h using existence-decider-fn-surjective? Should existence-decider-fn-surjective be more general?
      surj-h = existence-decider-fn-surjective
        (a ↦ b ↦ Lone(b) ∧ Desc(f(a))(b))
        (\x _ → f(x))
        (const ∘ invₗ-construction f g)
        unique-lone-descendant
        ⦃ intro (reflexivity(_≡_)) ⦄
        (\{z} → [∃]-intro (g(z)) ⦃ [∧]-intro
          (\{y} ([∧]-intro lone-y desc-y) → inverseₗ(g)(g⁻¹))
          -- ((\nepx → [⊥]-elim(nepx{z} ([∧]-intro (\{x} fxz → nepx{f(x)} ([∧]-intro (\{x'} p → {!!}) {!!})) ([∃]-intro 1 ⦃ reflexivity(_≡_) ⦄)))) ∘ [¬∃]-to-[∀¬])
          ((\nepx → Either.map1
              ((\([∃]-intro x ⦃ p ⦄) → {!!}) ∘ [∃]-map-proof [¬¬]-elim)
              (\p → [⊥]-elim(p{1} (reflexivity(_≡_))))
              (Either.map ([¬∀]-to-[∃¬] ⦃ classical ⦄ ⦃ classical ⦄) [¬∃]-to-[∀¬] ([¬]-preserves-[∧][∨]ᵣ (nepx{z})))
          ) ∘ [¬∃]-to-[∀¬])
        ⦄)
      -}

    instance
      inj-h : Injective(h)
      inj-h = existence-decider-fn-injective
        (a ↦ b ↦ Lone(b) ∧ Desc(f(a))(b))
        (\x _ → f(x))
        (const ∘ invₗ-construction f g)
        (\{x₁ x₂}{y₁ y₂} ([∧]-intro lone₁ desc₁) ([∧]-intro lone₂ desc₂) g⁻¹x₁g⁻¹x₂ →
          x₁            🝖[ _≡_ ]-[ inverᵣ-g⁻¹-specific lone₁ desc₁ ]-sym
          (g ∘ g⁻¹)(x₁) 🝖[ _≡_ ]-[ congruence₁(g) ⦃ func-g ⦄ g⁻¹x₁g⁻¹x₂ ]
          (g ∘ g⁻¹)(x₂) 🝖[ _≡_ ]-[ inverᵣ-g⁻¹-specific lone₂ desc₂ ]
          x₂            🝖-end
        )
        (\_ _ → Injective.proof inj-f)
        (\{
          {_} {_} {_}  ([∧]-intro lone₁ ([∃]-intro 𝟎       ⦃ desc₁ ⦄)) no g⁻¹x₁fx₂ → [⊥]-elim(lone₁ desc₁) ;
          {x₁}{x₂}{y₁} ([∧]-intro lone₁ ([∃]-intro (𝐒(n₁)) ⦃ desc₁ ⦄)) no g⁻¹x₁fx₂ → [⊥]-elim(no([∃]-intro y₁ ⦃ [∧]-intro lone₁ ([∃]-intro n₁ ⦃
            f(x₂)                      🝖[ _≡_ ]-[ g⁻¹x₁fx₂ ]-sym
            g⁻¹(x₁)                    🝖[ _≡_ ]-[ congruence₁(g⁻¹) (injective(f) ⦃ inj-f ⦄ desc₁) ]
            g⁻¹(g(((f ∘ g) ^ n₁)(y₁))) 🝖[ _≡_ ]-[ inverseₗ(g)(g⁻¹) ]
            ((f ∘ g) ^ n₁)(y₁)         🝖-end
          ⦄) ⦄))
        })

module _ where
  instance
    [≼][≍]-antisymmetry : ⦃ _ : ∀{ℓ}{P : Stmt{ℓ}} → Classical(P) ⦄ → Antisymmetry(_≼_ {ℓₑ}{ℓ})(_≍_)
    [≼][≍]-antisymmetry = intro [≼][≍]-antisymmetry-raw

  instance
    [≍]-reflexivity : Reflexivity(_≍_ {ℓₑ}{ℓ})
    Reflexivity.proof([≍]-reflexivity) = [∃]-intro(id) ⦃ [∧]-intro id-function id-bijective ⦄

  instance
    [≍]-symmetry : Symmetry(_≍_ {ℓₑ}{ℓ})
    Symmetry.proof [≍]-symmetry ([∃]-intro(f) ⦃ [∧]-intro f-function f-bijective ⦄) = ([∃]-intro(inv f) ⦃ [∧]-intro inv-function (inv-bijective ⦃ func = f-function ⦄) ⦄) where
      instance
        f-invertible : Invertible(f)
        f-invertible = bijective-to-invertible ⦃ bij = f-bijective ⦄

      instance
        invf-invertible : Invertible(inv f)
        ∃.witness invf-invertible = f
        ∃.proof invf-invertible = [∧]-intro f-function (Inverse-symmetry ([∧]-elimᵣ([∃]-proof f-invertible)))

  instance
    [≍]-transitivity : Transitivity(_≍_ {ℓₑ}{ℓ})
    Transitivity.proof([≍]-transitivity) ([∃]-intro(f) ⦃ [∧]-intro f-function f-bijective ⦄) ([∃]-intro(g) ⦃ [∧]-intro g-function g-bijective ⦄)
      = [∃]-intro(g ∘ f) ⦃ [∧]-intro
          ([∘]-function  {f = g}{g = f} ⦃ g-function ⦄ ⦃ f-function ⦄)
          ([∘]-bijective {f = g} ⦃ g-function ⦄ {g = f} ⦃ g-bijective ⦄ ⦃ f-bijective ⦄)
        ⦄

  instance
    [≍]-equivalence : Equivalence(_≍_ {ℓₑ}{ℓ})
    [≍]-equivalence = intro

  instance
    [≼]-reflexivity : Reflexivity(_≼_ {ℓₑ}{ℓ})
    Reflexivity.proof([≼]-reflexivity) = [∃]-intro(id) ⦃ [∧]-intro id-function id-injective ⦄

  instance
    [≼]-transitivity : Transitivity(_≼_ {ℓₑ}{ℓ})
    Transitivity.proof([≼]-transitivity) ([∃]-intro(f) ⦃ [∧]-intro f-function f-injective ⦄) ([∃]-intro(g) ⦃ [∧]-intro g-function g-injective ⦄)
      = [∃]-intro(g ∘ f) ⦃ [∧]-intro
          ([∘]-function  {f = g}{g = f} ⦃ g-function ⦄ ⦃ f-function ⦄)
          ([∘]-injective {f = g}{g = f} ⦃ g-injective ⦄ ⦃ f-injective ⦄)
        ⦄

  instance
    [≽]-reflexivity : Reflexivity(_≽_ {ℓₑ}{ℓ})
    Reflexivity.proof([≽]-reflexivity) = [∃]-intro(id) ⦃ [∧]-intro id-function id-surjective ⦄

  instance
    [≽]-transitivity : Transitivity(_≽_ {ℓₑ}{ℓ})
    Transitivity.proof([≽]-transitivity) ([∃]-intro(f) ⦃ [∧]-intro f-function f-surjective ⦄) ([∃]-intro(g) ⦃ [∧]-intro g-function g-surjective ⦄)
      = [∃]-intro(g ∘ f) ⦃ [∧]-intro
          ([∘]-function  {f = g}{g = f} ⦃ g-function ⦄ ⦃ f-function ⦄)
          ([∘]-surjective {f = g} ⦃ g-function ⦄ {g = f} ⦃ g-surjective ⦄ ⦃ f-surjective ⦄)
        ⦄

  open import Structure.Setoid.Size.Properties.Choice
  module _ ⦃ classical : ∀{ℓ}{P : Stmt{ℓ}} → Classical(P) ⦄ ⦃ surjChoice-ab : SurjectionInjectionChoice A B ⦄ ⦃ surjChoice-ba : SurjectionInjectionChoice B A ⦄ where
    [≽][≍]-antisymmetry-raw : (A ≽ B) → (B ≽ A) → (A ≍ B)
    [≽][≍]-antisymmetry-raw ab ba = [≼][≍]-antisymmetry-raw ([≽]-to-[≼] ba) ([≽]-to-[≼] ab)

  module _ ⦃ classical : ∀{ℓ}{P : Stmt{ℓ}} → Classical(P) ⦄ ⦃ surjChoice-ab : SurjectionInjectionChoice A B ⦄ where
    [≼][≽][≍]-antisymmetry-raw : (A ≼ B) → (A ≽ B) → (A ≍ B)
    [≼][≽][≍]-antisymmetry-raw lesser greater = [≼][≍]-antisymmetry-raw lesser ([≽]-to-[≼] greater)

  module _ ⦃ classical : ∀{ℓ}{P : Stmt{ℓ}} → Classical(P) ⦄ ⦃ surjChoice : ∀{ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂}{A : Setoid{ℓₑ₁}{ℓ₁}}{B : Setoid{ℓₑ₂}{ℓ₂}} → SurjectionInjectionChoice A B ⦄ where
    instance
      [≽][≍]-antisymmetry : Antisymmetry(_≽_ {ℓₑ}{ℓ})(_≍_)
      [≽][≍]-antisymmetry = intro [≽][≍]-antisymmetry-raw

    -- TODO: Totality of (_≼_).  Is this difficult to prove?
    -- [≼]-total : ((A ≼ B) ∨ (B ≼ A))


  open import Structure.Setoid.Universal

  -- The existence of a surjection from an injection for all sets implies excluded middle.
  [≼]-to-[≽]-for-inhabited-to-excluded-middle : (∀{ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂}{A : Setoid{ℓₑ₁}{ℓ₁}}{B : Setoid{ℓₑ₂}{ℓ₂}} → ⦃ ◊([∃]-witness A) ⦄ → (A ≼ B) → (B ≽ A)) → (∀{P : Type{ℓ}} → Classical(P))
  Classical.excluded-middle ([≼]-to-[≽]-for-inhabited-to-excluded-middle p {P = P}) = proof where
    open import Data.Boolean
    open import Data.Option
    open import Data.Option.Setoid
    open import Relator.Equals.Proofs.Equivalence
    f : Option(◊ P) → Bool
    f (Option.Some _) = 𝑇
    f Option.None     = 𝐹

    instance
      equiv-bool : Equiv(Bool)
      equiv-bool = [≡]-equiv

    instance
      equiv-pos-P : Equiv{Lvl.𝟎}(◊ P)
      equiv-pos-P = universal-equiv

    func-f : Function(f)
    Function.congruence func-f {None}   {None}   _ = reflexivity(_≡_ ⦃ [≡]-equiv ⦄)
    Function.congruence func-f {Some _} {Some _} _ = reflexivity(_≡_ ⦃ [≡]-equiv ⦄)

    inj-f : Injective(f)
    Injective.proof inj-f {None}   {None}   _ = <>
    Injective.proof inj-f {Some _} {Some _} _ = <>

    surjection : ([∃]-intro Bool ⦃ [≡]-equiv ⦄) ≽ ([∃]-intro (Option(◊ P)))
    surjection = p ⦃ intro ⦃ None ⦄ ⦄ ([∃]-intro f ⦃ [∧]-intro func-f inj-f ⦄)

    g : Bool → Option(◊ P)
    g = [∃]-witness surjection

    g-value-elim : ∀{y} → (g(𝑇) ≡ y) → (g(𝐹) ≡ y) → (∀{b} → (g(b) ≡ y))
    g-value-elim l r {𝑇} = l
    g-value-elim l r {𝐹} = r

    open Equiv(Option-equiv ⦃ equiv-pos-P ⦄) using () renaming (transitivity to Option-trans ; symmetry to Option-sym ; reflexivity to Option-refl)
    proof : (P ∨ ¬ P)
    proof with g(𝐹) | g(𝑇) | (\p → Surjective.proof ([∧]-elimᵣ([∃]-proof surjection)) {Some(intro ⦃ p ⦄)}) | g-value-elim{Option.None}
    ... | Some l | Some r | _    | _ = [∨]-introₗ (◊.inhabitant l)
    ... | Some l | None   | _    | _ = [∨]-introₗ (◊.inhabitant l)
    ... | None   | Some r | _    | _ = [∨]-introₗ (◊.inhabitant r)
    ... | None   | None   | surj | tttest = [∨]-introᵣ
      (\p → empty(transitivity(_≡_ {T = Option(◊ P)}) {Some(intro ⦃ p ⦄)} {g([∃]-witness(surj p))} {None}
        (symmetry(_≡_ {T = Option(◊ P)}) {g([∃]-witness(surj p))} ([∃]-proof(surj p)))
        (tttest <> <>)
      ))
      {-
        Some(intro ⦃ p ⦄)      🝖[ Equiv._≡_ Option-equiv ]-[ [∃]-proof(surj p) ]-sym
        g([∃]-witness(surj p)) 🝖[ Equiv._≡_ Option-equiv ]-[ tttest <> <> ]
        None                   🝖[ Equiv._≡_ Option-equiv ]-end
      -}

  {-module _ ⦃ surjChoice : ∀{A B : Setoid{ℓ}} → SurjectionInjectionChoice A B ⦄ where
    surjection-injection-choice-to-excluded-middle : ∀{P : Type{ℓ}} → Classical(P)
    Classical.excluded-middle (surjection-injection-choice-to-excluded-middle {P = P}) = {!!}
  -}

open import Logic.Propositional.Equiv
open import Structure.Relator
instance
  id-relator : UnaryRelator ⦃ intro _ ⦃ [≍]-equivalence{ℓ₁}{ℓ₂} ⦄ ⦄ [∃]-witness
  id-relator = UnaryRelator-introᵣ ⦃ _ ⦄ [∃]-witness
