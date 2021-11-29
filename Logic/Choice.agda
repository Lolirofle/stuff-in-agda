module Logic.Choice where

open import Data.Either as Either
open import Function
open import Functional.Instance
open import Logic.Propositional
import      Lvl
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Function
open import Syntax.Transitivity
open import Type
open import Type.Dependent
open import Type.Dependent.Equiv

{-
open import Type.Properties.Inhabited
-- TODO: Probably incorrect, but this is supposed to look like the usual formulation of the axiom of choice.
record Choice {ℓ₁ ℓ₂ ℓ₃} {I : Type{ℓ₁}} (C : (I → Type{ℓ₂}) → Type{ℓ₃}) : Type{ℓ₁ Lvl.⊔ Lvl.𝐒(ℓ₂) Lvl.⊔ ℓ₃} where
  field
    non-empty : ∀{P} → ◊(C(P))
    choice : (P : I → Type{ℓ₂}) → C(P) → Σ I P

  choose : (P : I → Type{ℓ₂}) → C(P) → I
  choose P cp = Σ.left(choice P cp)

  proof : ∀{P}{cp} → P(choose P cp)
  proof{P}{cp} = Σ.right(choice P cp)
-}

{-
open import Logic.Predicate
open import Structure.Function
open import Structure.Relator
record RelationalChoice {ℓ₁ ℓ₂ ℓ₃}
  (A : Type{ℓ₁})
  (B : A → Type{ℓ₂})
  (_▫_ : (a : A) → B(a) → Type{ℓ₃}) -- ⦃ rel : BinaryRelator(_▫_) ⦄
  : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}
  where

  field
    .non-empty : (a : A) → ∃(a ▫_)
    choose : (a : A) → B(a)
    proof : ∀{a} → (a ▫ (choose a))
-}

open import Logic.Predicate
open import Sets.PredicateSet as Set using (_∈_) renaming (PredSet to Set)
open import Structure.Function

-- The product of a non-empty indexed family of sets is non-empty.
-- I is the index for the family of sets.
-- S(i) for an (i : I) is a propositional subset of the type T.
-- Interpretation as finite product/tuple:
--   I is the indexing of the tuple.
--   T is the universe.
--   S is the product type. S(i) is the set that the element at the i:th position is a member of in the tuple.
--   choose is the construction of S. choose(i) is the element at the i:th position in the tuple.
--   Example (I = 𝕟(3) ; T = ℝ):
--     In function form:
--       S = (0 ↦ ℕ ; 1 ↦ ℤ ; 2 ↦ ℚ)
--       choose = (0 ↦ 5 ; 1 ↦ −3 ; 2 ↦ 2/9)
--     In tuple form:
--       S = ℕ ⨯ ℤ ⨯ ℚ
--       choose = (5 , −3 , 2/9)
record ProductChoice {ℓ₁ ℓ₂ ℓₛ ℓₑ₁ ℓₑ₂}
  (I : Type{ℓ₁}) ⦃ equiv-I : Equiv{ℓₑ₁}(I) ⦄
  (T : Type{ℓ₂}) ⦃ equiv-T : Equiv{ℓₑ₂}(T) ⦄
  (S : I → Set{ℓₛ}(T))
  ⦃ func-S : Function ⦃ equiv-I ⦄ ⦃ Set.[≡]-equiv ⦄ S ⦄
  (non-empty : ∀{i} → Set.NonEmpty(S(i)))
  : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓₛ Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓₑ₂}
  where

  field choice : (i : I) → Σ T (_∈ S(i))

  choose : I → T
  choose i = Σ.left(choice i)

  proof : ∀{i} → (choose i ∈ S(i))
  proof{i} = Σ.right(choice i)

  field ⦃ choose-function ⦄ : Function(choose)

-- open import Lang.Irrelevance.Convertable
record PredicateChoice {ℓₛ ℓ ℓₑ} (T : Type{ℓ}) ⦃ equiv : Equiv{ℓₑ}(T) ⦄ : Type{ℓ Lvl.⊔ Lvl.𝐒(ℓₛ) Lvl.⊔ ℓₑ} where
  -- field convertable-pred : (P : Set{ℓₛ}(T)) → Convertable(Σ T P)

  -- Note: The important part of the choice function is that it returns a new Σ-pair independent of the old one. The choice of expressing this as making the Σ-pair convertable is for convenience.
  field choice : (P : Set{ℓₛ}(T)) → (∃ P) → (Σ T P)
  -- choice P ep = convert(Σ T P) ⦃ convertable-pred(P) ⦄ ep

  choose : (P : Set{ℓₛ}(T)) → (∃ P) → T
  choose P ep = Σ.left(choice P ep)

  proof : ∀{P}{ep} → (choose P ep ∈ P)
  proof{P}{ep} = Σ.right(choice P ep)

  -- choose is a function with respect to set equality in the setoid of T.
  -- Note: This is the important part of PredicateChoice. Otherwise, one can just use the witness from the existential.
  field choose-function : ∀{P₁}{ep₁}{P₂}{ep₂} → (P₁ Set.≡ P₂) → (choose P₁ ep₁ ≡ choose P₂ ep₂)

open import Structure.Function.Domain

ProductChoiceAxiom = ∀{ℓ₁ ℓ₂ ℓₛ ℓₑ₁ ℓₑ₂}{I} ⦃ equiv-I : Equiv{ℓₑ₁}(I) ⦄ {T} ⦃ equiv-T : Equiv{ℓₑ₂}(T) ⦄ {S} ⦃ func-S ⦄ {ne : ∀{i} → Set.NonEmpty(S(i))} → ProductChoice{ℓ₁}{ℓ₂}{ℓₛ} I T S ⦃ func-S ⦄ ne
PredicateChoiceAxiom = ∀{ℓₛ ℓ ℓₑ}{T} ⦃ equiv : Equiv{ℓₑ}{ℓ}(T) ⦄ → PredicateChoice{ℓₛ}(T)
SurjectiveToInvertibleᵣAxiom = ∀{ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂}{A : Type{ℓ₁}} ⦃ equiv : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓ₂}} ⦃ equiv : Equiv{ℓₑ₂}(B) ⦄ {f : A → B} → Surjective(f) → Invertibleᵣ(f)
DisjointProductChoiceAxiom = (∀{ℓ₁ ℓ₂ ℓₛ ℓₑ₁ ℓₑ₂}{I} ⦃ equiv-I : Equiv{ℓₑ₁}(I) ⦄ {T} ⦃ equiv-T : Equiv{ℓₑ₂}(T) ⦄ {S} ⦃ func-S ⦄ {ne : ∀{i} → Set.NonEmpty(S(i))} {disjoint : ∀{i₁ i₂} → Set.Overlapping(S(i₁))(S(i₂)) → (i₁ ≡ i₂)} → ProductChoice{ℓ₁}{ℓ₂}{ℓₛ} I T S ⦃ func-S ⦄ ne)

module ProductChoiceAxiom(prod-choice : ProductChoiceAxiom) where
  open import Data.Tuple as Tuple using (_,_ ; _⨯_)

  product-to-predicate-choice : ProductChoiceAxiom → PredicateChoiceAxiom
  product-to-predicate-choice prod-choice {T = T} =
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

open import Structure.Setoid.Proofs

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
  open import Logic.Predicate
  open import Structure.Function
  open import Structure.Function.Domain.Proofs using (invᵣ-surjective)
  private variable ℓ : Lvl.Level
  private variable T A B : Type{ℓ}
  private variable f : A → B
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
  open import Data.Tuple as Tuple using (_⨯_ ; _,_)
  open import Data.Tuple.Equivalence
  open import Functional
  open import Lang.Irrelevance.Squash
  open import Logic.Predicate
  open import Structure.Function.Domain
  open import Structure.Relator.Equivalence.Proofs
  open import Type.Identity
  open import Type.Identity.Proofs  

  surjective-to-invertibleᵣ-to-disjoint-product-choice : DisjointProductChoiceAxiom
  surjective-to-invertibleᵣ-to-disjoint-product-choice {I = I}{T = T}{S = S} ⦃ func-S ⦄ {ne}{disjoint} =
    let ([∃]-intro f ⦃ [∧]-intro func-f invᵣ-f ⦄) = surj-invᵣ
                          {A = Σ(I ⨯ T) (\(i , x) → (x ∈ S(i)))} ⦃ Σₗ-equiv ⦄
                          {B = I}
                          {Tuple.left ∘ Σ.left}
                          (intro(\{i} → [∃]-intro ([∃]-elim (\{x} p → intro(i , x) p) (ne{i})) ⦃ reflexivity(_≡_) ⦄))
    in record{
      choice          = i ↦ intro (Tuple.right(Σ.left(f(i)))) ([↔]-to-[→] (congruence₁ ⦃ _ ⦄ ⦃ _ ⦄ (S) ⦃ func-S ⦄ (inverseᵣ _ _ ⦃ invᵣ-f ⦄)) (Σ.right(f(i)))) ;
      choose-function = intro(xy ↦ congruence₁(Tuple.right) (congruence₁ ⦃ _ ⦄ ⦃ _ ⦄ (f) ⦃ func-f ⦄ xy))}
  {-{ℓₛ = ℓₛ} {T = T} ⦃ equiv ⦄ =
    let -- invᵣ = surj-invᵣ
      instance
        test : ∀{P : T → Type{ℓₛ}} → Equiv(Σ T P)
        test{P} = intro ((_≡_) on₂ Σ.left) ⦃ on₂-equivalence{_▫_ = _≡_}{f = Σ.left} ⦃ Equiv.equivalence equiv ⦄ ⦄
      f : T → (T → Type)
      f o = {!!}
      {-
      surj-f : Surjective ⦃ Id-equiv ⦄ (f)
      surj-f = intro(\{P} → [∃]-intro (intro P id) ⦃ intro ⦄)
      ([∃]-intro f⁻¹ ⦃ [∧]-intro func-f⁻¹ invᵣ-f-f⁻¹ ⦄) = surj-invᵣ {A = Σ(T → Type)(P ↦ (Σ T P → Σ T P))} ⦃ Id-equiv ⦄ {B = T → Type} ⦃ Id-equiv ⦄ {f = f} surj-f
      -}
    in record {
      -- choice = P ↦ {!f⁻¹ P!} ;
      convertable-pred = P ↦ intro(\ep → {!!}) ;
      choice-function = \{P₁}{ep₁}{P₂}{ep₂} P₁P₂ → {!!} }
-}

module _ where
  open import Type.Identity
  open import Type.Identity.Proofs

  Id-product-choice : ∀{ℓ₁ ℓ₂ ℓₛ}{I}{T} {S} {ne : ∀{i} → Set.NonEmpty(S(i))} → ProductChoice{ℓ₁}{ℓ₂}{ℓₛ} I ⦃ Id-equiv ⦄ T ⦃ Id-equiv ⦄ S ⦃ Id-to-function ⦃ _ ⦄ ⦄ ne
  Id-product-choice {ne = ne} = record{
    choice          = i ↦ [∃]-elim (\{x} p → intro x p) (ne{i}) ;
    choose-function = Id-to-function ⦃ _ ⦄}
