module Sets.IterativeUSet where

import      Lvl
open import Structure.Setoid.WithLvl renaming (_≡_ to _≡ₛ_)
open import Type

private variable ℓ ℓₒ ℓₑ ℓ₁ ℓ₂ : Lvl.Level
private variable T Index Indexₗ Indexᵣ : Type{ℓ}
private variable a b c x y z : T

-- A model of constructive set theory (CZF) with atoms/urelements by iterative sets.
data IUset (T : Type{ℓₒ}) ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {ℓ} : Type{Lvl.𝐒(ℓ) ⊔ ℓₒ} where
  atom : T → IUset(T){ℓ}
  set  : ∀{Index : Type{ℓ}} → (Index → IUset(T){ℓ}) → IUset(T){ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  open import Functional
  open import Logic.Propositional
  open import Logic.Propositional.Theorems
  open import Logic.Predicate
  open import Syntax.Function

  private variable elem : Index → IUset(T) ⦃ equiv ⦄ {ℓ}

  data IsSet {ℓ} : IUset(T){ℓ} → Type{Lvl.of(T) ⊔ Lvl.𝐒(ℓ)} where
    intro : IsSet(set(elem))

  data IsAtom {ℓ} : IUset(T){ℓ} → Type{Lvl.of(T) ⊔ Lvl.𝐒(ℓ)} where
    intro : IsAtom(atom(x))

  data _≡_ {ℓ₁ ℓ₂} : IUset(T){ℓ₁} → IUset(T){ℓ₂} → Type{Lvl.𝐒(ℓ₁ ⊔ ℓ₂) ⊔ ℓₑ ⊔ Lvl.of(T)}
  data _⊆_ {ℓ₁ ℓ₂} : IUset(T){ℓ₁} → IUset(T){ℓ₂} → Type{Lvl.𝐒(ℓ₁ ⊔ ℓ₂) ⊔ ℓₑ ⊔ Lvl.of(T)}

  _⊇_ : IUset(T){ℓ₁} → IUset(T){ℓ₂} → Type
  A ⊇ B = B ⊆ A

  -- Equality is either equivalence on its atoms or by definition the antisymmetric property of the subset relation.
  data _≡_ where
    atom : ∀{a b} → (a ≡ₛ b) → (atom a ≡ atom b)
    set  : ∀{Indexₗ}{Indexᵣ}{elemₗ : Indexₗ → _}{elemᵣ : Indexᵣ → _} → (set elemₗ ⊇ set elemᵣ) → (set elemₗ ⊆ set elemᵣ) → (set elemₗ ≡ set elemᵣ)

  -- Set membership is the existence of an index in the set that points to a set equal element to the element.
  data _∈_ {ℓ₁ ℓ₂} (x : IUset(T){ℓ₁}) : IUset(T){ℓ₂} → Type{Lvl.𝐒(ℓ₁ ⊔ ℓ₂) ⊔ ℓₑ ⊔ Lvl.of(T)} where
    set : ∀{Index}{elem} → ∃{Obj = Index} (i ↦ x ≡ elem i) → (x ∈ set elem)

  -- Set subset is a mapping between the indices such that they point to the same element in both sets.
  data _⊆_ where
    set : ∀{Indexₗ}{Indexᵣ}{elemₗ : Indexₗ → _}{elemᵣ : Indexᵣ → _} → (map : Indexₗ → Indexᵣ) → (∀{i} → (elemₗ i ≡ elemᵣ (map i))) → (set elemₗ ⊆ set elemᵣ)

  _∉_ : IUset(T){ℓ₁} → IUset(T){ℓ₂} → Type
  a ∉ B = ¬(a ∈ B)

  Empty : ∀{ℓ₁ ℓ₂ : Lvl.Level} → IUset(T){ℓ₂} → Type
  Empty{ℓ₁}(A) = ∀{x : IUset(T){ℓ₁}} → (x ∉ A)

  private variable A B C : IUset(T) ⦃ equiv ⦄ {ℓ}

  atom-xor-set : IsAtom(A) ⊕ IsSet(A)
  atom-xor-set {A = atom _} = [⊕]-introₗ intro \()
  atom-xor-set {A = set  _} = [⊕]-introᵣ intro \()

  set-if-membership : (x ∈ A) → IsSet(A)
  set-if-membership (set _) = intro

  atom-is-empty : IsAtom(A) → Empty{ℓ}(A)
  atom-is-empty p = contrapositiveᵣ set-if-membership ([⊕]-not-left atom-xor-set p)

  open import Functional
  open import Structure.Relator.Equivalence
  open import Structure.Relator.Properties

  [≡]-reflexivity-raw : ∀{A : IUset(T){ℓ}} → (A ≡ A)
  [⊆]-reflexivity-raw : ∀{Index}{elem : Index → IUset(T){ℓ}} → (set elem ⊆ set elem)
  [⊇]-reflexivity-raw : ∀{Index}{elem : Index → IUset(T){ℓ}} → (set elem ⊇ set elem)
  [⊇]-reflexivity-raw = [⊆]-reflexivity-raw

  [≡]-reflexivity-raw {A = atom x} = atom(reflexivity(_≡ₛ_))
  [≡]-reflexivity-raw {A = set x}  = set [⊇]-reflexivity-raw [⊆]-reflexivity-raw

  [⊆]-reflexivity-raw {ℓ} {Index} {elem} = set id \{i} → [≡]-reflexivity-raw {A = elem(i)}

  [≡]-transitivity-raw : ∀{A B C : IUset(T){ℓ}} → (A ≡ B) → (B ≡ C) → (A ≡ C)
  [⊆]-transitivity-raw : ∀{A B C : IUset(T){ℓ}} → (A ⊆ B) → (B ⊆ C) → (A ⊆ C)
  [⊇]-transitivity-raw : ∀{A B C : IUset(T){ℓ}} → (A ⊇ B) → (B ⊇ C) → (A ⊇ C)
  [⊇]-transitivity-raw {A = A}{B = B}{C = C} ab bc = [⊆]-transitivity-raw {A = C}{B = B}{C = A} bc ab

  [≡]-transitivity-raw (atom ab)  (atom bc) = atom (transitivity(_≡ₛ_) ab bc)
  [≡]-transitivity-raw (set lab rab) (set lbc rbc) = set ([⊇]-transitivity-raw lab lbc) ([⊆]-transitivity-raw rab rbc)

  [⊆]-transitivity-raw (set {elemₗ = elem₁} {elem₂} mapₗ pₗ) (set {elemᵣ = elem₃} mapᵣ pᵣ) = set (mapᵣ ∘ mapₗ) \{i} → [≡]-transitivity-raw {A = elem₁ i}{B = elem₂(mapₗ i)} {C = elem₃(mapᵣ(mapₗ i))} pₗ pᵣ

  instance
    [≡]-reflexivity : Reflexivity(_≡_ {ℓ})
    [≡]-reflexivity = intro [≡]-reflexivity-raw
  instance
    [⊆]-reflexivity : Reflexivity{T = Index → IUset(T){ℓ}} ((_⊆_) on₂ set)
    [⊆]-reflexivity = intro [⊆]-reflexivity-raw
  instance
    [⊇]-reflexivity : Reflexivity{T = Index → IUset(T){ℓ}} ((_⊇_) on₂ set)
    [⊇]-reflexivity = intro [⊇]-reflexivity-raw
  instance
    [≡]-symmetry : Symmetry(_≡_ {ℓ})
    Symmetry.proof [≡]-symmetry (atom ab) = atom (symmetry(_≡ₛ_) ab)
    Symmetry.proof [≡]-symmetry (set l r) = set r l
  instance
    [⊆]-antisymmetry : Antisymmetry(_⊆_ {ℓ})(_≡_)
    Antisymmetry.proof [⊆]-antisymmetry l@(set _ _) r@(set _ _) = set r l
  instance
    [⊇]-antisymmetry : Antisymmetry(_⊇_ {ℓ})(_≡_)
    Antisymmetry.proof [⊇]-antisymmetry l@(set _ _) r@(set _ _) = set l r
  instance
    [≡]-transitivity : Transitivity(_≡_ {ℓ})
    [≡]-transitivity = intro [≡]-transitivity-raw
  instance
    [⊆]-transitivity : Transitivity(_⊆_ {ℓ})
    [⊆]-transitivity = intro [⊆]-transitivity-raw
  instance
    [⊇]-transitivity : Transitivity(_⊇_ {ℓ})
    [⊇]-transitivity = intro [⊇]-transitivity-raw
  instance
    [≡]-equivalence : Equivalence(_≡_ {ℓ})
    [≡]-equivalence = intro
  instance
    Iset-equiv : Equiv(IUset(T){ℓ})
    Equiv._≡_ Iset-equiv = _≡_
    Equiv.equivalence Iset-equiv = [≡]-equivalence

module Oper ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  open import Data renaming (Empty to EmptyType)
  open import Data.Boolean
  open import Data.Either as Either using ()
  open import Functional
  open import Type.Dependent

  -- The empty set, consisting of no elements.
  -- Index is the empty type, which means that there are no objects pointing to elements in the set.
  ∅ : IUset(T){ℓ}
  ∅ = set{Index = EmptyType} empty

  set-operator₁ : ∀{Index : ∀{I} → (I → IUset(T){ℓ}) → Type{ℓ}} → (∀{I} → (A : I → IUset(T){ℓ}) → (Index(A) → IUset(T){ℓ})) → (IUset(T){ℓ} → IUset(T){ℓ})
  set-operator₁ op (atom _) = ∅
  set-operator₁ op (set  A) = set (op A)

  set-operator₂ : ∀{Index : Type{ℓ} → Type{ℓ} → Type{ℓ}} → (∀{Iₗ Iᵣ} → (Iₗ → IUset(T){ℓ}) → (Iᵣ → IUset(T){ℓ}) → (Index(Iₗ)(Iᵣ) → IUset(T){ℓ})) → (IUset(T){ℓ} → IUset(T){ℓ} → IUset(T){ℓ})
  set-operator₂ op (atom _) (atom _) = ∅
  set-operator₂ op (atom _) (set  B) = set B
  set-operator₂ op (set  A) (atom _) = set A
  set-operator₂ op (set  A) (set  B) = set (op A B)

  -- The singleton set, consisting of one element.
  -- Index is the unit type, which means that there are a single object pointing to a single element in the set.
  singleton : IUset(T){ℓ} → IUset(T){ℓ}
  singleton = set{Index = Unit} ∘ const

  -- The pair set, consisting of two elements.
  -- Index is the boolean type, which means that there are two objects pointing to two elements in the set.
  pair : IUset(T){ℓ} → IUset(T){ℓ} → IUset(T){ℓ}
  pair A B = set{Index = Lvl.Up(Bool)} \{(Lvl.up 𝐹) → A ; (Lvl.up 𝑇) → B}

  -- The union operator.
  -- Index(A ∪ B) is the either type of two indices, which means that both objects from the A and the B index point to elements in the set.
  _∪_ : IUset(T){ℓ} → IUset(T){ℓ} → IUset(T){ℓ}
  _∪_ = set-operator₂(Either.map1)

{-
  -- The big union operator.
  -- Index(⋃ A) is the dependent sum type of an Index(A) and the index of the element this index points to.
  ⋃ : IUset(T){ℓ} → IUset(T){ℓ}
  ⋃ = set-operator₁{Index = {!!}} {!!}

  indexFilter : (A : IUset(T){ℓ}) → (Index(A) → Stmt{ℓ}) → IUset(T){ℓ}
  indexFilter A P = intro {Index = Σ(Index(A)) P} (elem(A) ∘ Σ.left)

  filter : (A : IUset(T)Iset{ℓ}) → (IUset(T){ℓ} → Stmt{ℓ}) → IUset(T){ℓ}
  filter{ℓ} A P = indexFilter A (P ∘ elem(A))

  indexFilterBool : (A : IUset(T){ℓ}) → (Index(A) → Bool) → IUset(T){ℓ}
  indexFilterBool A f = indexFilter A (Lvl.Up ∘ IsTrue ∘ f)

  filterBool : (A : IUset(T){ℓ}) → (IUset(T){ℓ} → Bool) → IUset(T){ℓ}
  filterBool A f = indexFilterBool A (f ∘ elem(A))
-}

open import Data
open import Data.Boolean
open import Data.Boolean.Proofs
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Proofs
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using ()
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Relator.Equals using () renaming (_≡_ to Id ; [≡]-intro to intro)
open import Structure.Setoid.WithLvl using (Equiv)
open import Structure.Function.Domain
open import Structure.Function
open import Structure.Relator
open import Syntax.Function
open import Syntax.Transitivity
open import Type.Dependent
