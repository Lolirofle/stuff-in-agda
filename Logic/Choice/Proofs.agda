module Logic.Choice.Proofs where

open import Data.Either as Either
open import Data.Tuple as Tuple using (_,_ ; _⨯_)
open import Data.Tuple.Equivalence
open import Function
open import Functional
open import Functional.Instance
open import Logic.Choice
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
open import Sets.PredicateSet as Set using (_∈_) renaming (PredSet to Set)
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Structure.Setoid
open import Structure.Setoid.Proofs
open import Syntax.Function
open import Syntax.Transitivity
open import Type
open import Type.Dependent.Sigma
open import Type.Dependent.Sigma.Equiv

module ProductChoiceAxiom(prod-choice : ProductChoiceAxiom) where
  product-to-predicate-choice : PredicateChoiceAxiom
  product-to-predicate-choice {T = T} =
    let
      open ProductChoice ⦃ _ ⦄ ⦃ func-S = _ ⦄ (prod-choice
        {I = Σ(T → Type) ∃} ⦃ Σₗ-equiv ⦃ Set.[≡]-equiv ⦄ ⦄
        {T = T}
        {\(intro P _) x → P(x)}
        ⦃ intro id ⦄
        {\{ {intro _ ep} → ep}})
    in record {
      choice          = P ↦ ep ↦ intro (choose(intro P ep)) (proof{intro P ep}) ;
      choose-function = congruence₁ ⦃ _ ⦄ ⦃ _ ⦄ (choose) ⦃ choose-function ⦄ }

  product-to-disjoint-product-choice : DisjointProductChoiceAxiom
  product-to-disjoint-product-choice = prod-choice

  open import Structure.Relator.Ordering
  open import Structure.Relator.Ordering.Lattice

  module _ {ℓ ℓₑ ℓₒ ℓₛ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ (_≤_ : T → T → Type{ℓₒ}) ⦃ ord : Weak.PartialOrder(_≤_) ⦄ where
    module _ (S : T → Type{ℓₛ}) where
      Chain : Type
      Chain = Weak.TotalOrder((_≤_) on₂ Σ.left{B = S}) ⦃ Σₗ-equiv ⦄

    -- Also called: Zorn's Lemma, Kuratowski-Zorn lemma
    MaxFromUpperBoundedChains : Type
    MaxFromUpperBoundedChains = (∀{S} → Chain(S) → ∃(LE.UpperBound(_≤_)(S))) → ∃(Weak.Properties.LE.Maximum(_≤_))

    

{-
module PredicateChoiceAxiom(predicate-choice : PredicateChoiceAxiom) where
  open import Data.Boolean
  open import Logic.Classical
  open import Logic.Propositional.Theorems
  open import Syntax.Implication
  open import Relator.Equals using ([≡]-intro)
  open import Relator.Equals.Proofs
  classical : ∀{ℓ}{P : Type{ℓ}} → Classical(P)
  classical {P = P} = intro ⦃$⦄
    let
      open PredicateChoice(predicate-choice{T = Bool})
      pos-ep = [∃]-intro 𝑇 ⦃ [∨]-introᵣ [≡]-intro ⦄
      neg-ep = [∃]-intro 𝐹 ⦃ [∨]-introᵣ [≡]-intro ⦄
      (intro pos-choose pos-choice) = choice(x ↦ P ∨ (x ≡ 𝑇)) pos-ep
      (intro neg-choose neg-choice) = choice(x ↦ P ∨ (x ≡ 𝐹)) neg-ep
    in
        • (
          (_⇒
            P                         ⇒-[ (\p → choose-function{ep₁ = pos-ep}{ep₂ = neg-ep} ([↔]-intro (const([∨]-introₗ p)) (const([∨]-introₗ p)))) ]
            (pos-choose ≡ neg-choose) ⇒-end
          ) ⇒
          (P → (pos-choose ≡ neg-choose))     ⇒-[ contrapositiveᵣ ]
          ((¬ P) ← (pos-choose ≢ neg-choose)) ⇒-end
        )
        • (
          • pos-choice
          • neg-choice
          ⇒₂-[ [∧]-intro ]
          (P ∨ (pos-choose ≡ 𝑇)) ∧ (P ∨ (neg-choose ≡ 𝐹)) ⇒-[ [↔]-to-[←] [∨][∧]-distributivityₗ ]
          P ∨ ((pos-choose ≡ 𝑇) ∧ (neg-choose ≡ 𝐹))       ⇒-[ Either.mapRight (\{([∧]-intro p0 n1) → subtransitivityᵣ(_≢_)(_≡_) (subtransitivityₗ(_≢_)(_≡_) p0 (\())) (symmetry(_≡_) n1)}) ]
          P ∨ (pos-choose ≢ neg-choose)                   ⇒-end
        )
        ⇒₂-[ Either.mapRight ]
        (P ∨ (¬ P)) ⇒-end

  open import Function.Domains
  open import Structure.Function.Domain.Proofs using (invᵣ-surjective)

  surjective-to-invertibleᵣ : SurjectiveToInvertibleᵣAxiom
  surjective-to-invertibleᵣ {A = A}{B = B}{f = f} surj = [∃]-intro f⁻¹ ⦃ [∧]-intro func invᵣ ⦄ where
    open PredicateChoice(predicate-choice{T = A})
    instance _ = surj

    ec = \y → [∃]-intro (invᵣ-surjective f(y)) ⦃ [∃]-proof(surjective(f)) ⦄
    c : (y : B) → Σ A (Fiber f(y))
    c(y) = choice(Fiber f(y)) (ec y)

    f⁻¹ : B → A
    f⁻¹(y) = Σ.left(c(y))

    invᵣ : Inverseᵣ(f)(f⁻¹)
    Inverseᵣ.proof invᵣ {y} = Σ.right(c(y))

    func : Function(f⁻¹)
    Function.congruence func {x}{y} xy = choose-function{ep₁ = ec x}{ep₂ = ec y} ([↔]-intro (_🝖 symmetry(_≡_) xy) (_🝖 xy))

  product-choice : ProductChoiceAxiom
  product-choice {I = I}{T = T}{S = S} ⦃ func-S ⦄ {ne} =
    let open PredicateChoice ⦃ _ ⦄ (predicate-choice{T = T})
    in record{
      choice          = i ↦ intro(choose(S(i)) (ne{i})) (proof{S(i)} {ne{i}});
      choose-function = intro (xy ↦ choose-function (congruence₁ ⦃ _ ⦄ ⦃ _ ⦄ (S) ⦃ func-S ⦄ xy))}

module SurjectiveToInvertibleᵣAxiom(surj-invᵣ : SurjectiveToInvertibleᵣAxiom) where
  open import Functional

  disjoint-product-choice : DisjointProductChoiceAxiom
  disjoint-product-choice {I = I}{T = T}{S = S} ⦃ func-S ⦄ {ne}{disjoint} =
    let ([∃]-intro f ⦃ [∧]-intro func-f invᵣ-f ⦄) = surj-invᵣ
                          {A = Σ(I ⨯ T) (\(i , x) → (x ∈ S(i)))} ⦃ Σₗ-equiv ⦄
                          {B = I}
                          {Tuple.left ∘ Σ.left}
                          (intro(\{i} → [∃]-intro ([∃]-elim (\{x} p → intro(i , x) p) (ne{i})) ⦃ reflexivity(_≡_) ⦄))
    in record{
      choice          = i ↦ intro (Tuple.right(Σ.left(f(i)))) ([↔]-to-[→] (congruence₁ ⦃ _ ⦄ ⦃ _ ⦄ (S) ⦃ func-S ⦄ (inverseᵣ _ _ ⦃ invᵣ-f ⦄)) (Σ.right(f(i)))) ;
      choose-function = intro(xy ↦ congruence₁(Tuple.right) (congruence₁ ⦃ _ ⦄ ⦃ _ ⦄ (f) ⦃ func-f ⦄ xy))}

module DisjointProductChoiceAxiom(prod-choice : DisjointProductChoiceAxiom) where
  distinct-product-choice : DistinctProductChoiceAxiom
  distinct-product-choice {I = I}{T = T}{S = S} ⦃ func-S ⦄ ⦃ inj-S ⦄ {ne} =
    let
      A : I → Set(Set(T) ⨯ T)
      A(i) = \(s , x) → (x ∈ s) ∧ (s Set.≡ S(i))

      ne-A : ∀{i} → Set.NonEmpty(A(i))
      ne-A{i} = [∃]-intro (S(i) , [∃]-witness (ne{i})) ⦃ [∧]-intro ([∃]-proof (ne{i})) (reflexivity(Set._≡_) ⦃ Set.[≡]-reflexivity ⦄ {S(i)}) ⦄

      func-A : Function ⦃ _ ⦄ ⦃ Set.[≡]-equiv ⦄(A)
      func-A =
        intro(\xy → [∧]-intro
          (Tuple.mapRight \p → transitivity(Set._≡_) p (\{a} → congruence₁ ⦃ _ ⦄ ⦃ _ ⦄ (S) ⦃ func-S ⦄ (symmetry(_≡_) xy) {a}))
          (Tuple.mapRight \p → transitivity(Set._≡_) p (\{a} → congruence₁ ⦃ _ ⦄ ⦃ _ ⦄ (S) ⦃ func-S ⦄ xy {a}))
        )

      disjoint-A : ∀{i₁ i₂} → Set.Overlapping(A(i₁))(A(i₂)) → (i₁ ≡ i₂)
      disjoint-A {i₁}{i₂} = \([∃]-intro (s , x) ⦃ [∧]-intro ([∧]-intro xs₁ sSi₁) ([∧]-intro xs₂ sSi₂) ⦄) → injective ⦃ _ ⦄ ⦃ _ ⦄ (S) ⦃ inj-S ⦄ (transitivity(Set._≡_) (symmetry(Set._≡_) (\{a} → sSi₁{a})) (\{a} → sSi₂{a}))

      open ProductChoice ⦃ _ ⦄  ⦃ _ ⦄ ⦃ func-S = _ ⦄ (prod-choice
        {I = I}
        {T = Set(T) ⨯ T} ⦃ Tuple-equiv ⦃ Set.[≡]-equiv{T = T} ⦄ ⦄
        {A}
        ⦃ func-A ⦄
        {ne-A}
        {disjoint-A})
    in record{
      choice          = i ↦ intro(Tuple.right(choose i)) ([↔]-to-[→] (Tuple.right(proof{i})) (Tuple.left(proof{i}))) ;
      choose-function = intro([∧]-elimᵣ ∘ Function.congruence ⦃ _ ⦄ ⦃ _ ⦄ choose-function) }

open import Function.Proofs
open import Structure.Relator.Equivalence.Proofs.On₂

module DistinctProductChoiceAxiom(prod-choice : DistinctProductChoiceAxiom) where
  product-choice : ProductChoiceAxiom
  product-choice {I = I}{T = T}{S = S} ⦃ func-S ⦄ {ne} =
    let
      equiv-IS : Equiv(I)
      equiv-IS = intro
        ((Set._≡_) on₂ S)
        ⦃ on₂-equivalence {f = S} ⦃ Set.[≡]-equivalence ⦄ ⦄

      -- Choosing an element of type T from a set of type Set(T) by equivalence classes of type I using (Set._≡_) on₂ S.
      -- This means that objects of type I are made equal when their corresponding sets are equal by using another equivalence on I.
      module One = ProductChoice ⦃ _ ⦄  ⦃ _ ⦄ ⦃ func-S = _ ⦄ (prod-choice
        {I = I} ⦃ equiv-IS ⦄
        {T = T}
        {S}
        ⦃ intro id ⦄
        ⦃ intro id ⦄
        {ne})

      -- Choosing an element from an equivalence class of type I using (Set._≡_) on₂ S.
      module Two = ProductChoice ⦃ _ ⦄  ⦃ _ ⦄ ⦃ func-S = _ ⦄ (prod-choice
        {I = I} ⦃ equiv-IS ⦄
        {T = I} ⦃ equiv-IS ⦄
        {(Set._≡_) on₂ S}
        ⦃ intro(i₁i₂ ↦ \{x} → [↔]-intro (transitivity(Set._≡_) (\{y} → i₁i₂{y})) (transitivity(Set._≡_) (symmetry(Set._≡_) (\{y} → i₁i₂{y})))) ⦄
        ⦃ intro(\{i₁}{i₂} → i₁i₂ ↦ \{x} → [↔]-to-[←] (i₁i₂{i₂}) (\{y} → reflexivity(Set._≡_) {S(i₂)}{y}) {x}) ⦄
        {\{i} → [∃]-intro i ⦃ reflexivity(Set._≡_) {S(i)} ⦄})
    in record{
      -- The choice function have an object of type I,
      -- then applies Two.choose to choose the canonical object representing the equivalence class of I,
      -- then applies One.choose to choose an element from the set represented by the canonical object above.
      -- In the end, this guarantees that the sets are equal when indices of type I are equal.
      -- Example:
      --   I = 𝕟(5)
      --   S = (
      --     0 ↦ {a}
      --     1 ↦ {a,b}
      --     2 ↦ {a,b,c}
      --     3 ↦ {a}
      --     4 ↦ {a,b}
      --   )
      --   In this example, the following indices should be made equal:
      --     0 = 3
      --     1 = 4
      --   By making equivalence classes of I based on set equality of S one will get the following result:
      --   S = (
      --     {0,3} ↦ {a}
      --     {1,4} ↦ {a,b}
      --     {2}   ↦ {a,b,c}
      --   )
      --   This is what intuitively happens.
      --   But what is actually happening is that the new choice function is constructed in the following way (as an example):
      --   choose = (
      --     0 ↦ One.choose(0)
      --     1 ↦ One.choose(1)
      --     2 ↦ One.choose(2)
      --     3 ↦ One.choose(0)
      --     4 ↦ One.choose(1)
      --   )
      --   if Two.choose is mapping 0 ↦ 3 and 1 ↦ 4.
      --   This makes the newly constructed choose function follow the equivalence class very obviously.
      choice = \i →
        let I = ProductChoice.choose ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ (prod-choice ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄) i
        in intro(One.choose(Two.choose i)) ([↔]-to-[←] (Two.proof{i} {One.choose I}) (One.proof{I})) ;
      choose-function = intro(xy ↦ congruence₁ ⦃ _ ⦄ _ ⦃ One.choose-function ⦄ (congruence₁ ⦃ _ ⦄ ⦃ _ ⦄ _ ⦃ Two.choose-function ⦄ (congruence₁ ⦃ _ ⦄ ⦃ _ ⦄ S ⦃ func-S ⦄ xy))) }

module _ where
  open import Type.Identity
  open import Type.Identity.Proofs

  Id-product-choice : ∀{ℓ₁ ℓ₂ ℓₛ}{I}{T} {S} {ne : ∀{i} → Set.NonEmpty(S(i))} → ProductChoice{ℓ₁}{ℓ₂}{ℓₛ} I ⦃ Id-equiv ⦄ T ⦃ Id-equiv ⦄ S ⦃ Id-to-function ⦃ _ ⦄ ⦄ ne
  Id-product-choice {ne = ne} = record{
    choice          = i ↦ [∃]-elim (\{x} p → intro x p) (ne{i}) ;
    choose-function = Id-to-function ⦃ _ ⦄}
-}
