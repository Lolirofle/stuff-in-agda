module Structure.Setoid.Size.Proofs where

open import Data
open import Data.Proofs
import      Data.Either        as Either
import      Data.Either.Proofs as Either
import      Lvl
open import Functional
open import Function.Proofs
open import Function.Inverseₗ
open import Function.Inverse
open import Function.Iteration
open import Lang.Instance
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
open import Type.Properties.Empty
open import Type.Properties.Inhabited
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable A B C : Setoid{ℓ}

module _ where
  instance
    [≍]-to-[≼] : (_≍_ {ℓ}) ⊆₂ (_≼_)
    _⊆₂_.proof [≍]-to-[≼] ([∃]-intro(f) ⦃ [∧]-intro f-function f-bijective ⦄) =
      ([∃]-intro(f) ⦃ [∧]-intro f-function (bijective-to-injective(f) ⦃ f-bijective ⦄) ⦄)

  instance
    [≍]-to-[≽] : (_≍_ {ℓ}) ⊆₂ (_≽_)
    _⊆₂_.proof [≍]-to-[≽] ([∃]-intro(f) ⦃ [∧]-intro f-function f-bijective ⦄) =
      ([∃]-intro(f) ⦃ [∧]-intro f-function (bijective-to-surjective(f) ⦃ f-bijective ⦄) ⦄)

  [≼]-empty-is-minimal : (([∃]-intro(Empty{ℓ})) ≼ A)
  [≼]-empty-is-minimal = [∃]-intro empty ⦃ [∧]-intro empty-function empty-injective ⦄

  [≽]-empty-is-not-minimal : ¬(∀{A : Setoid{ℓ}} → (A ≽ ([∃]-intro(Empty{ℓ}))))
  [≽]-empty-is-not-minimal proof with () ← [∃]-witness(proof {[∃]-intro Unit}) <>

  [≼]-to-[≽]-not-all : ¬((_≼_ {ℓ}) ⊆₂ swap(_≽_))
  [≼]-to-[≽]-not-all (intro proof) = [≽]-empty-is-not-minimal(proof [≼]-empty-is-minimal)

  [≼]-to-[≽]-for-inhabited : ⦃ _ : ∀{ℓ}{P : Stmt{ℓ}} → Classical(P) ⦄ ⦃ inh-A : (◊([∃]-witness A)) ⦄ → ((A ≼ B) → (B ≽ A))
  [≼]-to-[≽]-for-inhabited {A = [∃]-intro a} {B = [∃]-intro b} ([∃]-intro f ⦃ [∧]-intro f-func f-inj ⦄) = [∃]-intro (invₗ-construction(const [◊]-existence) f) ⦃ [∧]-intro (invₗ-construction-function ⦃ inj = f-inj ⦄) (inverseₗ-surjective ⦃ inverₗ = invₗ-construction-inverseₗ ⦃ inj = f-inj ⦄ ⦄) ⦄

  -- [≼][≽][≍]-antisymmetry : (A ≼ B) → (A ≽ B) → (A ≍ B)
  -- [≼][≽][≍]-antisymmetry ([∃]-intro f ⦃ f-inj ⦄) ([∃]-intro g ⦃ g-surj ⦄) = {!!}

-- TODO: This is variant of the "extensional axiom of choice" and it is unprovable in Agda. Though it is a possible axiom
-- instance
--   [≽]-to-[≼] : (A ≽ B) → (B ≼ A)
--   [≽]-to-[≼] ([∃]-intro(f) ⦃ [∧]-intro f-function f-surjective ⦄) =
--     ([∃]-intro(invᵣ f) ⦃ [∧]-intro (TODO: f-function) (invᵣ-injective ⦃ f-surjective ⦄) ⦄)

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

      {- TODO: This choice of h probably does not work for proving antisymmetry because nothing states that f and g are inverses, which seems to be neccessary in the proof
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

    surj-h : Surjective(h)
    Surjective.proof surj-h {b} with Either.map1-values{f = [∃]-witness}{g = const(f(g(b)))}{e = excluded-middle(∃(x ↦ g(x) ≡ g(b)))}
    ... | [∨]-introₗ ([∃]-intro ([∃]-intro b₂ ⦃ gb₂gb ⦄) ⦃ fgbb₂ ⦄) = [∃]-intro (g(b)) ⦃ fgbb₂ 🝖 injective(g) ⦃ inj-g ⦄ gb₂gb ⦄
    ... | [∨]-introᵣ([∃]-intro neggb ⦃ p ⦄) = [⊥]-elim(neggb ([∃]-intro b ⦃ reflexivity(_≡_) ⦄))

  instance
    -- TODO: Another attempt at antisymmetry from https://artofproblemsolving.com/wiki/index.php/Schroeder-Bernstein_Theorem
    postulate [≼][≍]-antisymmetry : ⦃ _ : ∀{ℓ}{P : Stmt{ℓ}} → Classical(P) ⦄ → Antisymmetry(_≼_ {ℓ})(_≍_)
    {-
    [≼][≍]-antisymmetry {A = A}{B = B} ([∃]-intro f ⦃ [∧]-intro func-f inj-f ⦄) ([∃]-intro g ⦃ [∧]-intro func-g inj-g ⦄) = [∃]-intro h ⦃ [∧]-intro func-h (injective-surjective-to-bijective(h)) ⦄ where
      Lone : [∃]-witness B → Stmt
      Lone(b) = ∀{a} → (f(a) ≢ b)

      Desc : [∃]-witness B → [∃]-witness B → Stmt
      Desc(b₁)(b₀) = ∃(n ↦ (b₁ ≡ ((f ∘ g) ^ n)(b₀)))

      h : [∃]-witness A → [∃]-witness B
      h(a) = Either.map1 [∃]-witness (const(f(a))) (excluded-middle(∃(b ↦ Lone(b) ∧ Desc(f(a))(b))))

      instance
        func-h : Function(h)
        Function.congruence func-h {a₁} {a₂} a₁a₂ with excluded-middle(∃(b ↦ Lone(b) ∧ Desc(f(a₁))(b))) | excluded-middle(∃(b ↦ Lone(b) ∧ Desc(f(a₂))(b))) | a₁a₂
        ... | [∨]-introₗ ([∃]-intro b₁ ⦃ [∧]-intro _ ([∃]-intro n₁ ⦃ gba1 ⦄) ⦄) | [∨]-introₗ ([∃]-intro b₂ ⦃ [∧]-intro _ ([∃]-intro n₂ ⦃ gba2 ⦄) ⦄) | _ = {!gba1 🝖 a₁a₂ 🝖 symmetry(_≡_) gba2!}
        ... | [∨]-introₗ ([∃]-intro b₁ ⦃ [∧]-intro _ ([∃]-intro n₁ ⦃ gba2 ⦄) ⦄) | [∨]-introᵣ ngba2                               | _ = {!!}
        ... | [∨]-introᵣ ngba1                               | [∨]-introₗ ([∃]-intro b₂ ⦃ [∧]-intro _ ([∃]-intro n₂ ⦃ gba2 ⦄) ⦄) | _ = {!!}
        ... | [∨]-introᵣ _                                   | [∨]-introᵣ _                                   | _ = {!!}

      instance
        surj-h : Surjective(h)
        Surjective.proof surj-h {y} with excluded-middle(∃(b ↦ Lone(b) ∧ Desc(y)(b)))
        ... | [∨]-introₗ x = {!!}
        ... | [∨]-introᵣ x = {!!}

      instance
        inj-h : Injective(h)
        Injective.proof inj-h = {!!}
  -}

  instance
    [≍]-reflexivity : Reflexivity(_≍_ {ℓ})
    Reflexivity.proof([≍]-reflexivity) = [∃]-intro(id) ⦃ [∧]-intro id-function id-bijective ⦄

  instance
    [≍]-symmetry : Symmetry(_≍_ {ℓ})
    Symmetry.proof [≍]-symmetry ([∃]-intro(f) ⦃ [∧]-intro f-function f-bijective ⦄) = ([∃]-intro(inv f) ⦃ [∧]-intro inv-function (inv-bijective ⦃ func = f-function ⦄) ⦄) where
      instance
        f-invertible : Invertible(f)
        f-invertible = bijective-to-invertible ⦃ bij = f-bijective ⦄

      instance
        invf-invertible : Invertible(inv f)
        ∃.witness invf-invertible = f
        ∃.proof invf-invertible = [∧]-intro f-function (Inverse-symmetry ([∧]-elimᵣ([∃]-proof f-invertible)))

  instance
    [≍]-transitivity : Transitivity(_≍_ {ℓ})
    Transitivity.proof([≍]-transitivity) ([∃]-intro(f) ⦃ [∧]-intro f-function f-bijective ⦄) ([∃]-intro(g) ⦃ [∧]-intro g-function g-bijective ⦄)
      = [∃]-intro(g ∘ f) ⦃ [∧]-intro
          ([∘]-function  {f = g}{g = f} ⦃ g-function ⦄ ⦃ f-function ⦄)
          ([∘]-bijective {f = g} ⦃ g-function ⦄ {g = f} ⦃ g-bijective ⦄ ⦃ f-bijective ⦄)
        ⦄

  instance
    [≍]-equivalence : Equivalence(_≍_ {ℓ})
    [≍]-equivalence = intro

  instance
    [≼]-reflexivity : Reflexivity(_≼_ {ℓ})
    Reflexivity.proof([≼]-reflexivity) = [∃]-intro(id) ⦃ [∧]-intro id-function id-injective ⦄

  instance
    [≼]-transitivity : Transitivity(_≼_ {ℓ})
    Transitivity.proof([≼]-transitivity) ([∃]-intro(f) ⦃ [∧]-intro f-function f-injective ⦄) ([∃]-intro(g) ⦃ [∧]-intro g-function g-injective ⦄)
      = [∃]-intro(g ∘ f) ⦃ [∧]-intro
          ([∘]-function  {f = g}{g = f} ⦃ g-function ⦄ ⦃ f-function ⦄)
          ([∘]-injective {f = g}{g = f} ⦃ g-injective ⦄ ⦃ f-injective ⦄)
        ⦄

  instance
    [≽]-reflexivity : Reflexivity(_≽_ {ℓ})
    Reflexivity.proof([≽]-reflexivity) = [∃]-intro(id) ⦃ [∧]-intro id-function id-surjective ⦄

  instance
    [≽]-transitivity : Transitivity(_≽_ {ℓ})
    Transitivity.proof([≽]-transitivity) ([∃]-intro(f) ⦃ [∧]-intro f-function f-surjective ⦄) ([∃]-intro(g) ⦃ [∧]-intro g-function g-surjective ⦄)
      = [∃]-intro(g ∘ f) ⦃ [∧]-intro
          ([∘]-function  {f = g}{g = f} ⦃ g-function ⦄ ⦃ f-function ⦄)
          ([∘]-surjective {f = g} ⦃ g-function ⦄ {g = f} ⦃ g-surjective ⦄ ⦃ f-surjective ⦄)
        ⦄

  module _ (A : Setoid{ℓ₁}) (B : Setoid{ℓ₂}) where
    record SurjectionChoice : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : (A ≽ B) → (B ≼ A)
    [≽]-to-[≼] = inst-fn SurjectionChoice.proof

  module _ ⦃ surjChoice : SurjectionChoice A B ⦄ where
    --(A ≼ B) → (B ≼ A) → (A ≍ B)
