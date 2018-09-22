open import Logic.Classical.NaturalDeduction

module Logic.Classical.SetTheory.ZFC {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} {Proof} {Construct} ⦃ predicateEqTheory : PredicateEq.Theory{ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} (Proof) (Construct) ⦄ (_∈_ : Domain → Domain → Stmt) where

open import Functional hiding (Domain)
open import Lang.Instance
import      Lvl
-- open        Logic.Classical.NaturalDeduction.Propositional {ℓₗ Lvl.⊔ ℓₒ}{ℓₘₗ Lvl.⊔ ℓₘₒ}{Stmt}          (Proof)             hiding (Theory)
-- open        Logic.Classical.NaturalDeduction.Predicate     {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ}           {Stmt} {Domain} (Proof) (Construct) hiding (Theory)
open        Logic.Classical.NaturalDeduction.PredicateEq   {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ}           {Stmt} {Domain} (Proof) (Construct) renaming (Theory to PredicateEqTheory)
open        PredicateEqTheory (predicateEqTheory)

-- The statement that the set s is empty
Empty : Domain → Stmt
Empty(s) = ∀ₗ(x ↦ ¬(x ∈ s))

-- The statement that the set s is non-empty
NonEmpty : Domain → Stmt
NonEmpty(s) = ∃ₗ(x ↦ (x ∈ s))

-- The statement that the sets s₁ and s₂ are disjoint
Disjoint : Domain → Domain → Stmt
Disjoint(s₁)(s₂) = ¬ ∃ₗ(x ↦ (x ∈ s₁)∧(x ∈ s₂))

-- The statement that the predicate F is a partial function
PartialFunction : (Domain → Domain → Stmt) → Domain → Stmt
PartialFunction(F) (dom) = ∀ₗ(x ↦ (x ∈ dom) ⟶ Unique(y ↦ F(x)(y)))

-- The statement that the predicate F is a total function
TotalFunction : (Domain → Domain → Stmt) → Domain → Stmt
TotalFunction(F) (dom) = ∀ₗ(x ↦ (x ∈ dom) ⟶ ∃ₗ!(y ↦ F(x)(y)))

-- The statement that the set s is a function
-- FunctionSet : Domain → Stmt
-- FunctionSet(s) = ∀ₗ(x ↦ ∃ₗ!(y ↦ (x , y) ∈ s))

_∋_ : Domain → Domain → Stmt
_∋_ a x = (x ∈ a)

_∌_ : Domain → Domain → Stmt
_∌_ a x = ¬(x ∈ a)

_∉_ : Domain → Domain → Stmt
_∉_ x a = ¬(x ∈ a)

_⊆_ : Domain → Domain → Stmt
_⊆_ a b = ∀ₗ(x ↦ (x ∈ a) ⟶ (x ∈ b))

_⊇_ : Domain → Domain → Stmt
_⊇_ a b = ∀ₗ(x ↦ (x ∈ a) ⟵ (x ∈ b))

record Signature : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ (ℓₘₗ Lvl.⊔ ℓₘₒ)) where
  field
    ∅ : Domain
    pair : Domain → Domain → Domain
    filter : Domain → (Domain → Stmt) → Domain
    ℘ : Domain → Domain
    ⋃ : Domain → Domain
    inductiveSet : Domain

  singleton : Domain → Domain
  singleton(s) = pair(s)(s)

  _∪_ : Domain → Domain → Domain
  a ∪ b = ⋃(pair a b)

  _∩_ : Domain → Domain → Domain
  a ∩ b = filter(a)(_∈ b)

  _∖_ : Domain → Domain → Domain
  a ∖ b = filter(a)(_∉ b)

  ⋂ : Domain → Domain
  ⋂(a) = filter(⋃(a)) (a₁ ↦ ∀ₗ(a₂ ↦ (a₂ ∈ a) ⟶ (a₁ ∈ a₂)))

  𝟎 : Domain
  𝟎 = ∅

  𝐒 : Domain → Domain
  𝐒(n) = n ∪ singleton(n)

  _,_ : Domain → Domain → Domain
  a , b = pair(singleton(a)) (pair(a)(b))

  _⨯_ : Domain → Domain → Domain
  a ⨯ b = filter(℘(℘(a ∪ b))) (t ↦ ∃ₗ(x ↦ (x ∈ a) ∧ ∃ₗ(y ↦ (y ∈ b) ∧ t ≡ (x , y))))

module Axioms ⦃ signature : Signature ⦄ where
  open Signature ⦃ ... ⦄

  -- A set which is empty exists.
  -- • Allows a construction of the empty set.
  EmptySet = Proof(Empty(∅))

  -- A set with two elements exists.
  -- • Allows a construction of a set with two elements.
  Pairing = Proof(∀ₗ(x₁ ↦ ∀ₗ(x₂ ↦ (∀ₗ(x ↦ (x ∈ pair(x₁)(x₂)) ⟷ (x ≡ x₁)∨(x ≡ x₂))))))

  -- A set which is the subset of a set where all elements satisfies a predicate exists.
  RestrictedComprehension = ∀{φ : Domain → Stmt} → Proof(∀ₗ(s ↦ ∀ₗ(x ↦ ((x ∈ filter(s)(φ)) ⟷ ((x ∈ s) ∧ φ(x))))))

  -- A set which contains all the subsets of a set exists.
  -- • Allows a construction of a set that is the powerset of a set.
  PowerSet = Proof(∀ₗ(s ↦ ∀ₗ(x ↦ (x ∈ ℘(s)) ⟷ (x ⊆ s))))

  -- A set which contains all the elements of a group of sets exists.
  -- • Allows a construction of a set that is the union of some sets.
  Union = Proof(∀ₗ(ss ↦ ∀ₗ(x ↦ (x ∈ ⋃(ss)) ⟷ ∃ₗ(s ↦ (s ∈ ss)∧(x ∈ s)))))

  -- An infinite set (specifically, a ℕ-inductive set (which just happens to be infinite)) exists.
  Infinity = Proof((𝟎 ∈ inductiveSet) ∧ ∀ₗ(n ↦ (n ∈ inductiveSet) ⟶ (𝐒(n) ∈ inductiveSet)))

  -- Set equality is determined by its contents.
  -- • Guarantees the definition of equality for sets.
  Extensionality = Proof(∀ₗ(s₁ ↦ ∀ₗ(s₂ ↦ ∀ₗ(x ↦ (x ∈ s₁)⟷(x ∈ s₂)) ⟷ (s₁ ≡ s₂))))

  -- A non-empty set contain sets that are disjoint to it.
  -- • Prevents sets containing themselves.
  -- • Making every set have an ordinal rank.
  Regularity = Proof(∀ₗ(s₁ ↦ (NonEmpty(s₁) ⟶ ∃ₗ(s₂ ↦ (s₂ ∈ s₁) ∧ Disjoint(s₁)(s₂)))))

  Replacement = ∀{φ : Domain → Domain → Stmt} → Proof(∀ₗ(A ↦ TotalFunction(φ)(A) ⟶ ∃ₗ(B ↦ ∀ₗ(y ↦ (y ∈ B) ⟷ ∃ₗ(x ↦ (x ∈ A) ∧ φ(x)(y))))))

  Choice = Proof(⊤)

record ZF ⦃ signature : Signature ⦄ : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ (ℓₘₗ Lvl.⊔ ℓₘₒ)) where
  open Axioms
  open Signature ⦃ ... ⦄

  field
    extensional   : Extensionality
    empty         : EmptySet
    regular       : Regularity
    comprehension : RestrictedComprehension
    pairing       : Pairing
    union         : Union
    replacement   : Replacement
    infinity      : Infinity
    power         : PowerSet

record ZFC ⦃ signature : Signature ⦄ : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ (ℓₘₗ Lvl.⊔ ℓₘₒ)) where
  open Axioms
  open Signature ⦃ ... ⦄

  field
    extensional   : Extensionality
    empty         : EmptySet
    regular       : Regularity
    comprehension : RestrictedComprehension
    pairing       : Pairing
    union         : Union
    replacement   : Replacement
    infinity      : Infinity
    power         : PowerSet
    choice        : Choice

module Proofs ⦃ signature : Signature ⦄ ⦃ axioms : ZF ⦄ where
  open Axioms
  open Signature ⦃ ... ⦄
  open ZF ⦃ ... ⦄

  [∅]-containment : Proof(∀ₗ(x ↦ (x ∈ ∅) ⟷ ⊥))
  [∅]-containment =
    ([∀]-intro (\{x} →
      ([↔]-intro
        ([⊥]-elim)
        ([⊥]-intro
          ([∀]-elim empty{x})
        )
      )
    ))

  pair-containment : Proof(∀ₗ(a₁ ↦ ∀ₗ(a₂ ↦ (∀ₗ(x ↦ (x ∈ pair(a₁)(a₂)) ⟷ (x ≡ a₁)∨(x ≡ a₂))))))
  pair-containment = pairing

  filter-containment : ∀{φ : Domain → Stmt} → Proof(∀ₗ(s ↦ ∀ₗ(x ↦ ((x ∈ filter(s)(φ)) ⟷ ((x ∈ s) ∧ φ(x))))))
  filter-containment = comprehension

  [℘]-containment : Proof(∀ₗ(s ↦ ∀ₗ(x ↦ (x ∈ ℘(s)) ⟷ (x ⊆ s))))
  [℘]-containment = power

  [⋃]-containment : Proof(∀ₗ(ss ↦ ∀ₗ(x ↦ (x ∈ ⋃(ss)) ⟷ ∃ₗ(s ↦ (s ∈ ss)∧(x ∈ s)))))
  [⋃]-containment = union

  singleton-containment : Proof(∀ₗ(a ↦ ∀ₗ(x ↦ (x ∈ singleton(a)) ⟷ (x ≡ a))))
  singleton-containment =
    ([∀]-intro (\{a} →
      ([∀]-intro (\{x} →
        [↔].transitivity
          ([∀]-elim([∀]-elim([∀]-elim(pair-containment){a}){a}){x})
          ([↔]-intro ([∨].redundancyₗ) ([∨].redundancyᵣ))
      ))
    ))

  [↔]-with-[∧]ₗ : ∀{a₁ a₂ b} → Proof(a₁ ⟷ a₂) → Proof((a₁ ∧ b) ⟷ (a₂ ∧ b))
  [↔]-with-[∧]ₗ (proof) =
    ([↔]-intro
      (a₂b ↦ [∧]-intro (([↔]-elimₗ proof) ([∧]-elimₗ a₂b)) ([∧]-elimᵣ a₂b))
      (a₁b ↦ [∧]-intro (([↔]-elimᵣ proof) ([∧]-elimₗ a₁b)) ([∧]-elimᵣ a₁b))
    )

  [↔]-with-[∧]ᵣ : ∀{a b₁ b₂} → Proof(b₁ ⟷ b₂) → Proof((a ∧ b₁) ⟷ (a ∧ b₂))
  [↔]-with-[∧]ᵣ (proof) =
    ([↔]-intro
      (ab₂ ↦ [∧]-intro ([∧]-elimₗ ab₂) (([↔]-elimₗ proof) ([∧]-elimᵣ ab₂)))
      (ab₁ ↦ [∧]-intro ([∧]-elimₗ ab₁) (([↔]-elimᵣ proof) ([∧]-elimᵣ ab₁)))
    )

  [↔]-with-[∧] : ∀{a₁ a₂ b₁ b₂} → Proof(a₁ ⟷ a₂) → Proof(b₁ ⟷ b₂) → Proof((a₁ ∧ b₁) ⟷ (a₂ ∧ b₂))
  [↔]-with-[∧] (a₁a₂) (b₁b₂) =
    ([↔]-intro
      (a₂b₂ ↦ [∧]-intro (([↔]-elimₗ a₁a₂) ([∧]-elimₗ a₂b₂)) (([↔]-elimₗ b₁b₂) ([∧]-elimᵣ a₂b₂)))
      (a₁b₁ ↦ [∧]-intro (([↔]-elimᵣ a₁a₂) ([∧]-elimₗ a₁b₁)) (([↔]-elimᵣ b₁b₂) ([∧]-elimᵣ a₁b₁)))
    )

  [↔]-with-[∨]ₗ : ∀{a₁ a₂ b} → Proof(a₁ ⟷ a₂) → Proof((a₁ ∨ b) ⟷ (a₂ ∨ b))
  [↔]-with-[∨]ₗ (proof) =
    ([↔]-intro
      ([∨]-elim([∨]-introₗ ∘ ([↔]-elimₗ proof)) [∨]-introᵣ)
      ([∨]-elim([∨]-introₗ ∘ ([↔]-elimᵣ proof)) [∨]-introᵣ)
    )

  [↔]-with-[∨]ᵣ : ∀{a b₁ b₂} → Proof(b₁ ⟷ b₂) → Proof((a ∨ b₁) ⟷ (a ∨ b₂))
  [↔]-with-[∨]ᵣ (proof) =
    ([↔]-intro
      ([∨]-elim [∨]-introₗ ([∨]-introᵣ ∘ ([↔]-elimₗ proof)))
      ([∨]-elim [∨]-introₗ ([∨]-introᵣ ∘ ([↔]-elimᵣ proof)))
    )

  [↔]-with-[∨] : ∀{a₁ a₂ b₁ b₂} → Proof(a₁ ⟷ a₂) → Proof(b₁ ⟷ b₂) → Proof((a₁ ∨ b₁) ⟷ (a₂ ∨ b₂))
  [↔]-with-[∨] (a₁a₂) (b₁b₂) =
    ([↔]-intro
      ([∨]-elim ([∨]-introₗ ∘ ([↔]-elimₗ a₁a₂)) ([∨]-introᵣ ∘ ([↔]-elimₗ b₁b₂)))
      ([∨]-elim ([∨]-introₗ ∘ ([↔]-elimᵣ a₁a₂)) ([∨]-introᵣ ∘ ([↔]-elimᵣ b₁b₂)))
    )

  [↔]-with-[∀] : ∀{f g} → (∀{x} → Proof(f(x) ⟷ g(x))) → Proof((∀ₗ f) ⟷ (∀ₗ g))
  [↔]-with-[∀] (proof) =
    ([↔]-intro
      (allg ↦ [∀]-intro(\{x} → [↔]-elimₗ (proof{x}) ([∀]-elim(allg){x})))
      (allf ↦ [∀]-intro(\{x} → [↔]-elimᵣ (proof{x}) ([∀]-elim(allf){x})))
    )

  [↔]-with-[∃] : ∀{f g} → (∀{x} → Proof(f(x) ⟷ g(x))) → Proof((∃ₗ f) ⟷ (∃ₗ g))
  [↔]-with-[∃] (proof) =
    ([↔]-intro
      ([∃]-elim(\{x} → gx ↦ [∃]-intro{_}{x}([↔]-elimₗ (proof{x}) (gx))))
      ([∃]-elim(\{x} → fx ↦ [∃]-intro{_}{x}([↔]-elimᵣ (proof{x}) (fx))))
    )

  postulate [∨][∧]-distributivityₗ : ∀{a b c} → Proof((a ∨ (b ∧ c)) ⟷ (a ∨ b)∧(a ∨ c))
  postulate [∨][∧]-distributivityᵣ : ∀{a b c} → Proof(((a ∧ b) ∨ c) ⟷ (a ∨ c)∧(b ∨ c))
  postulate [∧][∨]-distributivityₗ : ∀{a b c} → Proof((a ∧ (b ∨ c)) ⟷ (a ∧ b)∨(a ∧ c))
  postulate [∧][∨]-distributivityᵣ : ∀{a b c} → Proof(((a ∨ b) ∧ c) ⟷ (a ∧ c)∨(b ∧ c))
  postulate [≡]-substitute-this-is-almost-trivial : ∀{φ : Domain → Stmt}{a b} → Proof(((a ≡ b) ∧ φ(a)) ⟷ φ(b))

  [∪]-containment : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ∪ b)) ⟷ (x ∈ a)∨(x ∈ b)))))
  [∪]-containment =
    ([∀]-intro (\{a} →
      ([∀]-intro (\{b} →
        ([∀]-intro (\{x} →
          ([∀]-elim([∀]-elim [⋃]-containment{pair(a)(b)}){x})
          〔ₗ [↔].transitivity 〕
          ([↔]-with-[∃] (\{s} →
            ([↔]-with-[∧]ₗ ([∀]-elim([∀]-elim([∀]-elim pair-containment{a}){b}){s}))
            〔ₗ [↔].transitivity 〕
            ([∧][∨]-distributivityᵣ)
            〔ₗ [↔].transitivity 〕
            [↔]-with-[∨] ([≡]-substitute-this-is-almost-trivial) ([≡]-substitute-this-is-almost-trivial)
          ))
          〔ₗ [↔].transitivity 〕
          ([↔]-intro ([∃].redundancyₗ) ([∃].redundancyᵣ))
        ))
      ))
    ))

  [∩]-containment : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ∩ b)) ⟷ (x ∈ a)∧(x ∈ b)))))
  [∩]-containment =
    ([∀]-intro (\{a} →
      ([∀]-intro (\{b} →
        ([∀]-elim(filter-containment){a})
      ))
    ))


  [∖]-containment : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ∖ b)) ⟷ (x ∈ a)∧(x ∉ b)))))
  [∖]-containment =
    ([∀]-intro (\{a} →
      ([∀]-intro (\{b} →
        ([∀]-elim(filter-containment){a})
      ))
    ))

  -- [⋂]-containment : Proof(∀ₗ(ss ↦ ∀ₗ(x ↦ (x ∈ ⋂(ss)) ⟷ ∀ₗ(s ↦ (s ∈ ss) ⟶ (x ∈ s)))))
  -- [⋂]-containment = union

  -- [⨯]-containment : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ⨯ b)) ⟷ ∃ₗ(x₁ ↦ ∃ₗ(x₂ ↦ x ≡ (x₁ , x₂)))))))
  -- [⨯]-containment =

  -- [⋃]-max : Proof(∀ₗ(s ↦ ∀ₗ(max ↦ ∀ₗ(x ↦ (x ∈ (⋃ s)) ⟶ (x ⊆ max)) ⟶ ((⋃ s) ≡ max))))

  -- [⋃][℘]-inverse : Proof(∀ₗ(s ↦ ⋃(℘(s)) ≡ s))

  ∀ₛ : Domain → (Domain → Stmt) → Stmt
  ∀ₛ(S)(φ) = ∀ₗ(x ↦ (x ∈ S) ⟶ φ(x))

  ∃ₛ : Domain → (Domain → Stmt) → Stmt
  ∃ₛ(S)(φ) = ∃ₗ(x ↦ (x ∈ S) ∧ φ(x))

  module Structure where
    module Function where
      Function : Set(_)
      Function = (Domain → Domain)

      record Type (f : Function) : Set(ℓₒ) where
        constructor intro
        field
          domain   : Domain
          codomain : Domain

        map : Domain → Domain
        map a = filter(codomain)(y ↦ ∃ₛ(a)(x ↦ y ≡ f(x)))

        ⊶ : Domain
        ⊶ = map(domain)
      open Type ⦃ ... ⦄ public

      module Properties where
        Closed : (f : Function) → ⦃ _ : Type(f) ⦄ → Stmt
        Closed(f) = ∀ₛ(domain{f})(x ↦ f(x) ∈ codomain{f})

        Injective : (f : Function) → ⦃ _ : Type(f) ⦄ → Stmt
        Injective(f) = ∀ₛ(domain{f})(x ↦ ∀ₛ(domain{f})(y ↦ (f(x) ≡ f(y)) ⟶ (x ≡ y)))

        Surjective : (f : Function) → ⦃ _ : Type(f) ⦄ → Stmt
        Surjective(f) = ∀ₛ(codomain{f})(y ↦ ∃ₛ(domain{f})(x ↦ y ≡ f(x)))

        Bijective : (f : Function) → ⦃ _ : Type(f) ⦄ → Stmt
        Bijective(f) = Injective(f) ∧ Surjective(f)

    module Relator where
      UnaryRelator : Set(_)
      UnaryRelator = (Domain → Stmt)

      BinaryRelator : Set(_)
      BinaryRelator = (Domain → Domain → Stmt)

      -- Quotient set
      _/_ : Domain → BinaryRelator → Domain
      a / (_▫_) = filter(℘(a))(aₛ ↦ ∀ₛ(aₛ)(x ↦ ∀ₛ(aₛ)(y ↦ x ▫ y)))

      -- Equivalence class
      [_of_,_] : Domain → Domain → BinaryRelator → Domain
      [ x of a , (_▫_) ] = filter(a)(y ↦ x ▫ y)

      module Properties where
        Reflexivity : Domain → BinaryRelator → Stmt
        Reflexivity(S)(_▫_) = ∀ₛ(S)(x ↦ x ▫ x)

        Irreflexivity : Domain → BinaryRelator → Stmt
        Irreflexivity(S)(_▫_) = ∀ₛ(S)(x ↦ ¬(x ▫ x))

        Symmetry : Domain → BinaryRelator → Stmt
        Symmetry(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y) ⟶ (y ▫ x)))

        Asymmetry : Domain → BinaryRelator → Stmt
        Asymmetry(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y) ⟶ ¬(y ▫ x)))

        Antisymmetry : Domain → BinaryRelator → Stmt
        Antisymmetry(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (y ▫ x)∧(x ▫ y) ⟶ (x ≡ y)))

        Transitivity : Domain → BinaryRelator → Stmt
        Transitivity(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ ∀ₛ(S)(z ↦ (x ▫ y)∧(y ▫ z) ⟶ (x ▫ z))))

        Equivalence  : Domain → BinaryRelator → Stmt
        Equivalence(S)(_▫_) = Reflexivity(S)(_▫_) ∧ Symmetry(S)(_▫_) ∧ Transitivity(S)(_▫_)

  module Numeral where
    module Natural where
      open Structure
      open Structure.Function.Properties
      open Structure.Relator
      open Structure.Relator.Properties

      Inductive : Domain → Stmt
      Inductive(I) = (∅ ∈ I) ∧ (∀ₗ(x ↦ (x ∈ I) ⟶ (𝐒(x) ∈ I)))

      [∩]-inductive : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (Inductive(a) ∧ Inductive(b)) ⟶ Inductive(a ∩ b))))
      [∩]-inductive =
        ([∀]-intro (\{a} →
          ([∀]-intro (\{b} →
            ([→]-intro(indaindb ↦
              ([∧]-intro
                -- ∅ is in
                ([↔]-elimₗ
                  ([∀]-elim([∀]-elim([∀]-elim([∩]-containment){a}){b}){∅})
                  ([∧]-intro
                    ([∧]-elimₗ([∧]-elimₗ indaindb))
                    ([∧]-elimₗ([∧]-elimᵣ indaindb))
                  )
                )

                -- 𝐒 is in
                ([∀]-intro (\{x} →
                  ([→]-intro(x∈a∩b ↦
                    ([↔]-elimₗ
                      ([∀]-elim([∀]-elim([∀]-elim([∩]-containment){a}){b}){𝐒(x)})
                      ([∧]-intro
                        -- 𝐒(x) ∈ a
                        ([→]-elim([∀]-elim([∧]-elimᵣ([∧]-elimₗ indaindb)){x})(
                          -- x ∈ a
                          [∧]-elimₗ([↔]-elimᵣ
                            ([∀]-elim([∀]-elim([∀]-elim([∩]-containment){a}){b}){x})
                            (x∈a∩b)
                          )
                        ))

                        -- 𝐒(x) ∈ b
                        ([→]-elim([∀]-elim([∧]-elimᵣ([∧]-elimᵣ indaindb)){x})(
                          -- x ∈ b
                          [∧]-elimᵣ([↔]-elimᵣ
                            ([∀]-elim([∀]-elim([∀]-elim([∩]-containment){a}){b}){x})
                            (x∈a∩b)
                          )
                        ))
                      )
                    )
                  ))
                ))
              )
            ))
          ))
        ))

      -- postulate [⋂]-property : ∀{φ} → Proof(∀ₗ(s ↦ ∀ₗ(x ↦ (x ∈ s) ⟶ φ(x)) ⟶ φ(⋂ s))) TODO: MAybe not true
      postulate [⋂]-inductive : Proof(∀ₗ(s ↦ ∀ₗ(x ↦ (x ∈ s) ⟶ Inductive(x)) ⟶ Inductive(⋂ s)))

      ℕ : Domain
      ℕ = ⋂(filter(℘(inductiveSet)) Inductive) -- TODO: This pattern seems useful

      [ℕ]-inductive : Proof(Inductive(ℕ))
      [ℕ]-inductive =
        ([→]-elim
          ([∀]-elim
            [⋂]-inductive
            {filter(℘(inductiveSet)) Inductive}
          )
          ([∀]-intro(\{x} →
            ([→]-intro(x∈filter ↦
              [∧]-elimᵣ(([↔]-elimᵣ([∀]-elim([∀]-elim filter-containment{℘(inductiveSet)}){x})) (x∈filter))
            ))
          ))
        )

      -- postulate any : ∀{l}{a : Set(l)} → a

      postulate [ℕ]-elements : Proof(∀ₛ(ℕ)(n ↦ (n ≡ 𝟎) ∨ ∃ₛ(ℕ)(p ↦ n ≡ 𝐒(p))))

      _<_ : BinaryRelator
      a < b = a ∈ b

      _≤_ : BinaryRelator
      a ≤ b = (a < b) ∨ (a ≡ b)

      _>_ : BinaryRelator
      a > b = b < a

      _≥_ : BinaryRelator
      a ≥ b = b ≤ a

      postulate [<]-irreflexivity : Proof(Irreflexivity(ℕ)(_<_))
      postulate [<]-asymmetry     : Proof(Antisymmetry(ℕ)(_<_))
      postulate [<]-transitivity  : Proof(Transitivity(ℕ)(_<_))

      postulate [≤]-reflexivity  : Proof(Irreflexivity(ℕ)(_≤_))
      postulate [≤]-antisymmetry : Proof(Antisymmetry(ℕ)(_≤_))
      postulate [≤]-transitivity : Proof(Transitivity(ℕ)(_≤_))

      instance
        [𝐒]-type : Function.Type(𝐒)
        [𝐒]-type = Function.Type.intro ℕ ℕ

      postulate [𝐒]-injective : Proof(Injective(𝐒))

      -- ∀ₛ(ℕ)(a ↦ ∀ₛ(ℕ)(b ↦ (a < b) ⟶ (𝐒(a) < 𝐒(b))))
      -- ∀ₛ(ℕ)(a ↦ ∀ₛ(ℕ)(b ↦ (a < b) ⟶ (𝐒(a) < 𝐒(b))))
      -- ∀ₛ(ℕ)(n ↦ 𝟎 ≢ 𝐒(n))
