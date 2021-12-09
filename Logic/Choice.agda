module Logic.Choice where

open import Logic.Predicate
import      Lvl
open import Sets.PredicateSet as Set using (_∈_) renaming (PredSet to Set)
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Relator
open import Structure.Relator.Function using (Total)
open import Structure.Setoid
open import Type
open import Type.Dependent

record Choice {ℓ₁ ℓ₂ ℓₒₚ ℓₑ₁ ℓₑ₂}
  {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  (_⟼_ : A → B → Type{ℓₒₚ})
  ⦃ rel : BinaryRelator(_⟼_) ⦄
  ⦃ total : Total(_⟼_) ⦄
  : Type{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓₒₚ Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓₑ₂}
  where

  field choice : (a : A) → Σ B (a ⟼_)

  choose : A → B
  choose i = Σ.left(choice i)

  proof : ∀{a} → (a ⟼ choose(a))
  proof{a} = Σ.right(choice a)

  field ⦃ choose-function ⦄ : Function(choose)

-- The product of a non-empty indexed family of sets is non-empty.
-- I is the index for the family of sets.
-- S(i) for an (i : I) is a propositional subset of the type T.
-- Interpretation as a product/tuple (when finite):
--   I is the indexing of the tuple elements.
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
-- Interpretation as a function choosing an element satisfying a predicate:
--   choose(i) is a construction of an object satisfying S(i).
--   choose itself is a function with respect to the setoid.
--   The parameterization indicates that the choose function may be different for different S, which means that there need not to be an unique choice function for all types and indexed families of sets.
record ProductChoice {ℓ₁ ℓ₂ ℓₛ ℓₑ₁ ℓₑ₂}
  (I : Type{ℓ₁}) ⦃ equiv-I : Equiv{ℓₑ₁}(I) ⦄
  (T : Type{ℓ₂}) ⦃ equiv-T : Equiv{ℓₑ₂}(T) ⦄
  (S : I → Set{ℓₛ}(T)) -- TODO: Is it necessary for the set to be a relation with respect to the setoid? If it is, use Sets.ExtensionalPredicateSet instead
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

{- TODO: When formulating ProductChoice using types directly. Is this actually useful? Or even equivalent to the other formulations?
open import Structure.Setoid.Size
open import Type.Properties.Inhabited
record FunctionChoice {ℓ ℓᵢ ℓₑᵢ ℓₑₛ}
  (I : Type{ℓᵢ}) ⦃ equiv-I : Equiv{ℓₑᵢ}(I) ⦄
  (S : I → Type{ℓ}) ⦃ equiv-S : ∀{i} → Equiv{ℓₑₛ}(S(i)) ⦄
  ⦃ func-S : ∀{i₁ i₂} → (i₁ ≡ i₂) → ([∃]-intro(S(i₁)) ⦃ equiv-S{i₁} ⦄ ≍ [∃]-intro(S(i₂)) ⦃ equiv-S{i₂} ⦄) ⦄
  (non-empty : ∀{i} → ◊(S(i)))
  : Type{ℓ Lvl.⊔ ℓᵢ Lvl.⊔ ℓₑᵢ Lvl.⊔ ℓₑₛ}
  where

  field
    choose : (i : I) → S(i)
    choose-function : ∀{i₁ i₂} → (eq : i₁ ≡ i₂) → ([∃]-witness(func-S eq) (choose(i₁)) ≡ choose(i₂))
-}

-- A mapping from non-empty propositional subsets of a type T to one of its elements is a function.
record PredicateChoice {ℓₛ ℓ ℓₑ} (T : Type{ℓ}) ⦃ equiv : Equiv{ℓₑ}(T) ⦄ : Type{ℓ Lvl.⊔ Lvl.𝐒(ℓₛ) Lvl.⊔ ℓₑ} where
  -- Note: The important part of the choice function is that it returns a new Σ-pair that may be different than the witness in the existential.
  field choice : (P : Set{ℓₛ}(T)) → (∃ P) → (Σ T P)

  choose : (P : Set{ℓₛ}(T)) → (∃ P) → T
  choose P ep = Σ.left(choice P ep)

  proof : ∀{P}{ep} → (choose P ep ∈ P)
  proof{P}{ep} = Σ.right(choice P ep)

  -- choose is a function with respect to set equality in the setoid of T.
  -- Note: This is the important part of PredicateChoice. Otherwise, one can just use the witness from the existential.
  field choose-function : ∀{P₁}{ep₁}{P₂}{ep₂} → (P₁ Set.≡ P₂) → (choose P₁ ep₁ ≡ choose P₂ ep₂)

{-
record TypeChoice {ℓₛ ℓ ℓₑ} : Type{ℓ Lvl.⊔ Lvl.𝐒(ℓₛ) Lvl.⊔ ℓₑ} where
  field
    choice : (P : Type{ℓ}) ⦃ equiv : Equiv{ℓₑ}(P) ⦄ → .P → P
    choose-function : ∀{P₁} ⦃ equiv₁ : Equiv{ℓₑ}(P₁) ⦄ {e₁}{P₂} ⦃ equiv₂ : Equiv{ℓₑ}(P₂) ⦄ {e₂} → (eq : P₁ ≍ P₂) → (UnaryRelator.substitute(id-relator) (choose P₁ e₁) eq ≡ choose P₂ e₂)
-}

PredicateChoiceAxiom =
  ∀{ℓₛ ℓ ℓₑ}{T} ⦃ equiv : Equiv{ℓₑ}{ℓ}(T) ⦄ →
  PredicateChoice{ℓₛ}(T)

SurjectiveToInvertibleᵣAxiom =
  ∀{ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂}
  {A : Type{ℓ₁}} ⦃ equiv : Equiv{ℓₑ₁}(A) ⦄
  {B : Type{ℓ₂}} ⦃ equiv : Equiv{ℓₑ₂}(B) ⦄
  {f : A → B} →
  Surjective(f) → Invertibleᵣ(f)

ProductChoiceAxiom =
  ∀{ℓ₁ ℓ₂ ℓₛ ℓₑ₁ ℓₑ₂}
  {I} ⦃ equiv-I ⦄
  {T} ⦃ equiv-T ⦄
  {S} ⦃ func-S ⦄
  {ne : ∀{i} → Set.NonEmpty(S(i))} →
  ProductChoice{ℓ₁}{ℓ₂}{ℓₛ}{ℓₑ₁}{ℓₑ₂} I ⦃ equiv-I ⦄ T ⦃ equiv-T ⦄ S ⦃ func-S ⦄ ne

DistinctProductChoiceAxiom =
  ∀{ℓ₁ ℓ₂ ℓₛ ℓₑ₁ ℓₑ₂}
  {I} ⦃ equiv-I ⦄
  {T} ⦃ equiv-T ⦄
  {S} ⦃ func-S ⦄ ⦃ inj-S : Injective ⦃ equiv-I ⦄ ⦃ Set.[≡]-equiv ⦄ (S) ⦄
  {ne : ∀{i} → Set.NonEmpty(S(i))} →
  ProductChoice{ℓ₁}{ℓ₂}{ℓₛ}{ℓₑ₁}{ℓₑ₂} I ⦃ equiv-I ⦄ T ⦃ equiv-T ⦄ S ⦃ func-S ⦄ ne

DisjointProductChoiceAxiom =
  ∀{ℓ₁ ℓ₂ ℓₛ ℓₑ₁ ℓₑ₂}
  {I} ⦃ equiv-I ⦄
  {T} ⦃ equiv-T ⦄
  {S} ⦃ func-S ⦄
  {ne : ∀{i} → Set.NonEmpty(S(i))}
  {disjoint : ∀{i₁ i₂} → Set.Overlapping(S(i₁))(S(i₂)) → (i₁ ≡ i₂)} →
  ProductChoice{ℓ₁}{ℓ₂}{ℓₛ}{ℓₑ₁}{ℓₑ₂} I ⦃ equiv-I ⦄ T ⦃ equiv-T ⦄ S ⦃ func-S ⦄ ne

ChoiceAxiom =
  ∀{ℓ₁ ℓ₂ ℓₒₚ ℓₑ₁ ℓₑ₂}
  {A} ⦃ equiv-A ⦄
  {B} ⦃ equiv-B ⦄
  {_⟼_}
  ⦃ rel ⦄
  ⦃ total ⦄ →
  Choice{ℓ₁}{ℓ₂}{ℓₒₚ}{ℓₑ₁}{ℓₑ₂} {A} ⦃ equiv-A ⦄ {B} ⦃ equiv-B ⦄ (_⟼_) ⦃ rel ⦄ ⦃ total ⦄
