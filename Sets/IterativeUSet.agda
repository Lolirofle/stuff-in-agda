module Sets.IterativeUSet where

open import Data renaming (Empty to EmptyType)
open import Functional
import      Lvl
open import Structure.Setoid.WithLvl renaming (_≡_ to _≡ₛ_)
open import Syntax.Function
open import Type
open import Type.Dependent

private variable ℓ ℓₒ ℓₑ ℓ₁ ℓ₂ : Lvl.Level
private variable T Indexₗ Indexᵣ : Type{ℓ}
private variable a b c x y z : T

-- A model of constructive set theory with atoms/urelements (CZFU) by iterative sets.
-- The definition states that an instance of IUset is either an atom or a set.
-- An atom is an instance of the atoms/urelements.
-- A set is an instance of a set container which is a function from a type of indices (which depends on the set) to an IUset. The function should be interpreted as pointing to every element of the set, and the image of this function is how a single set is represented.
module _ (T : Type{ℓₒ}) ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {ℓ} where
  data IUset : Type{Lvl.𝐒(ℓ) Lvl.⊔ ℓₒ}
  SetContainer : Type{Lvl.𝐒(ℓ) Lvl.⊔ ℓₒ}
  SetContainer = Σ(Type{ℓ}) (_→ᶠ IUset)
  data IUset where
    atom : T → IUset
    set  : SetContainer → IUset

module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {ℓ} where
  pattern setc {Index} elem = set(intro Index elem)

  module SetContainer where
    -- The projection of the index type for a set container.
    Index : (SC : SetContainer(T){ℓ}) → type-of(Σ.left SC)
    Index = Σ.left

    -- The projection of the elements' function for a set container.
    elem : (SC : SetContainer(T){ℓ}) → type-of(Σ.right SC)
    elem = Σ.right

  -- The projection of the index type for an IUset's set container if it is a set.
  -- It is non-existant otherwise (modeled by the empty type with no inhabitants).
  Index : IUset(T){ℓ} → Type{ℓ}
  Index (atom x) = EmptyType
  Index (set SC) = SetContainer.Index SC

  -- The projection of the elements' function for an IUset's set container it if it a set.
  -- It is non-existant otherwise (modeled by the empty function which is interpreted as the empty set).
  elem : (A : IUset(T){ℓ}) → (Index(A) → IUset(T){ℓ})
  elem (atom _) ()
  elem (set SC) = SetContainer.elem SC

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  open import Functional
  open import Logic.Propositional
  open import Logic.Propositional.Theorems
  open import Logic.Predicate

  private variable SC SCₗ SCᵣ : SetContainer(T) ⦃ equiv ⦄ {ℓ}

  -- The predicate stating that an IUset is a set.
  data IsSet {ℓ} : IUset(T){ℓ} → Type{Lvl.of(T) Lvl.⊔ Lvl.𝐒(ℓ)} where
    intro : IsSet(set(SC))

  -- The predicate stating that an IUset is an atom.
  data IsAtom {ℓ} : IUset(T){ℓ} → Type{Lvl.of(T) Lvl.⊔ Lvl.𝐒(ℓ)} where
    intro : IsAtom(atom(x))

  data _≡_ {ℓ₁ ℓ₂} : IUset(T){ℓ₁} → IUset(T){ℓ₂} → Type{Lvl.𝐒(ℓ₁ Lvl.⊔ ℓ₂) Lvl.⊔ ℓₑ Lvl.⊔ Lvl.of(T)}
  data _⊆_ {ℓ₁ ℓ₂} : IUset(T){ℓ₁} → IUset(T){ℓ₂} → Type{Lvl.𝐒(ℓ₁ Lvl.⊔ ℓ₂) Lvl.⊔ ℓₑ Lvl.⊔ Lvl.of(T)}

  _⊇_ : IUset(T){ℓ₁} → IUset(T){ℓ₂} → Type
  A ⊇ B = B ⊆ A

  -- Equality is either equivalence on its atoms or by definition the antisymmetric property of the subset relation.
  data _≡_ where
    atom : (a ≡ₛ b) → (atom a ≡ atom b)
    set  : (set SCₗ ⊇ set SCᵣ) → (set SCₗ ⊆ set SCᵣ) → (set SCₗ ≡ set SCᵣ)

  -- Set membership is the existence of an index in the set that points to a set equal element to the element.
  -- Note: This is never satisfied for an atom on the right.
  data _∈_ {ℓ₁ ℓ₂} (x : IUset(T){ℓ₁}) : IUset(T){ℓ₂} → Type{Lvl.𝐒(ℓ₁ Lvl.⊔ ℓ₂) Lvl.⊔ ℓₑ Lvl.⊔ Lvl.of(T)} where
    set : ∃{Obj = SetContainer.Index(SC)} (i ↦ x ≡ SetContainer.elem(SC) i) → (x ∈ set SC)
  [∈]-proof : (x ∈ set SC) → ∃{Obj = SetContainer.Index(SC)} (i ↦ x ≡ SetContainer.elem(SC) i)
  [∈]-proof (set p) = p
  [∈]-index : (x ∈ set SC) → SetContainer.Index(SC)
  [∈]-index (set ([∃]-intro i)) = i
  [∈]-elem : (p : (x ∈ set SC)) → (x ≡ SetContainer.elem(SC) ([∈]-index p))
  [∈]-elem (set ([∃]-intro _ ⦃ p ⦄)) = p

  -- Set subset is a mapping between the indices such that they point to the same element in both sets.
  -- Note: This is never satisfied for an atom on the right.
  data _⊆_ where
    set : (map : SetContainer.Index(SCₗ) → SetContainer.Index(SCᵣ)) → (∀{i} → (SetContainer.elem(SCₗ) i ≡ SetContainer.elem(SCᵣ) (map i))) → (set SCₗ ⊆ set SCᵣ)
  [⊆]-map : (set SCₗ ⊆ set SCᵣ) → (SetContainer.Index(SCₗ) → SetContainer.Index(SCᵣ))
  [⊆]-map (set map _) = map
  [⊆]-proof : (p : (set SCₗ ⊆ set SCᵣ)) → (∀{i} → (SetContainer.elem(SCₗ) i ≡ SetContainer.elem(SCᵣ) ([⊆]-map p i)))
  [⊆]-proof (set _ p) = p

  -- The binary relation of non-membership.
  _∉_ : IUset(T){ℓ₁} → IUset(T){ℓ₂} → Type
  a ∉ B = ¬(a ∈ B)

  -- The predicate stating that an IUset contains no elements (in other words, is empty).
  Empty : ∀{ℓ₁ ℓ₂ : Lvl.Level} → IUset(T){ℓ₂} → Type
  Empty{ℓ₁}(A) = ∀{x : IUset(T){ℓ₁}} → (x ∉ A)

  open import Logic.Classical

  private variable A B C : IUset(T) ⦃ equiv ⦄ {ℓ}

  instance
    -- An IUset is exclusively either an atom or a set.
    atom-xor-set : IsAtom(A) ⊕ IsSet(A)
    atom-xor-set {A = atom _} = [⊕]-introₗ intro \()
    atom-xor-set {A = set  _} = [⊕]-introᵣ intro \()

  instance
    IsAtom-classical : Classical₁(IsAtom{ℓ})
    IsAtom-classical = classical-from-xorₗ

  instance
    IsSet-classical : Classical₁(IsSet{ℓ})
    IsSet-classical = classical-from-xorᵣ

  -- An IUset containing something is always a set.
  set-if-membership : (x ∈ A) → IsSet(A)
  set-if-membership (set _) = intro

  -- An IUset which is an atom is always "empty" when interpreted as a set.
  atom-is-empty : IsAtom(A) → Empty{ℓ}(A)
  atom-is-empty p = contrapositiveᵣ set-if-membership ([⊕]-not-left atom-xor-set p)

  open import Functional
  open import Structure.Relator.Equivalence
  open import Structure.Relator.Properties

  [≡]-reflexivity-raw : (A ≡ A)
  [⊆]-reflexivity-raw : (set SC ⊆ set SC)
  [⊇]-reflexivity-raw : (set SC ⊇ set SC)
  [⊇]-reflexivity-raw = [⊆]-reflexivity-raw

  [≡]-reflexivity-raw {A = atom x} = atom(reflexivity(_≡ₛ_))
  [≡]-reflexivity-raw {A = set x}  = set [⊇]-reflexivity-raw [⊆]-reflexivity-raw

  [⊆]-reflexivity-raw {SC = SC} = set id \{i} → [≡]-reflexivity-raw {A = SetContainer.elem(SC)(i)}

  [≡]-transitivity-raw : (A ≡ B) → (B ≡ C) → (A ≡ C)
  [⊆]-transitivity-raw : (A ⊆ B) → (B ⊆ C) → (A ⊆ C)
  [⊇]-transitivity-raw : (A ⊇ B) → (B ⊇ C) → (A ⊇ C)
  [⊇]-transitivity-raw {A = A}{B = B}{C = C} ab bc = [⊆]-transitivity-raw {A = C}{B = B}{C = A} bc ab

  [≡]-transitivity-raw (atom ab)  (atom bc) = atom (transitivity(_≡ₛ_) ab bc)
  [≡]-transitivity-raw (set lab rab) (set lbc rbc) = set ([⊇]-transitivity-raw lab lbc) ([⊆]-transitivity-raw rab rbc)

  [⊆]-transitivity-raw (set {SCₗ = SC₁} {SCᵣ = SC₂} mapₗ pₗ) (set {SCᵣ = SC₃} mapᵣ pᵣ) = set (mapᵣ ∘ mapₗ) \{i} → [≡]-transitivity-raw {A = SetContainer.elem(SC₁) i}{B = SetContainer.elem(SC₂)(mapₗ i)} {C = SetContainer.elem(SC₃)(mapᵣ(mapₗ i))} pₗ pᵣ

  instance
    [≡]-reflexivity : Reflexivity(_≡_ {ℓ})
    [≡]-reflexivity = intro [≡]-reflexivity-raw
  instance
    [⊆]-reflexivity : Reflexivity{T = SetContainer(T){ℓ}} ((_⊆_) on₂ set)
    [⊆]-reflexivity = intro [⊆]-reflexivity-raw
  instance
    [⊇]-reflexivity : Reflexivity{T = SetContainer(T){ℓ}} ((_⊇_) on₂ set)
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



  [≡]-to-[⊆] : (set SCₗ ≡ set SCᵣ) → (set SCₗ ⊆ set SCᵣ)
  [≡]-to-[⊆] (set l r) = r

  [≡]-to-[⊇] : (set SCₗ ≡ set SCᵣ) → (set SCₗ ⊇ set SCᵣ)
  [≡]-to-[⊇] (set l r) = l

  [∈]-of-elem : ∀{A : IUset(T){ℓ}}{ia : Index(A)} → (elem(A)(ia) ∈ A)
  [∈]-of-elem {A = setc {Index} elem} {ia} = set ([∃]-intro ia ⦃ [≡]-reflexivity-raw ⦄)

  [⊆]-membership : ((_⊆_ on₂ set) SCₗ SCᵣ) ← (∀{x : IUset(T)} → (x ∈ set SCₗ) → (x ∈ set SCᵣ))
  [⊆]-membership {SCₗ = SCₗ} {SCᵣ = SCᵣ} proof = set
    (ia    ↦ [∃]-witness ([∈]-proof(proof {elem(set SCₗ)(ia)} ([∈]-of-elem {A = set SCₗ}))))
    (\{ia} → [∃]-proof   ([∈]-proof(proof {elem(set SCₗ)(ia)} ([∈]-of-elem {A = set SCₗ}))))

module Oper ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  open import Data renaming (Empty to EmptyType)
  open import Data.Boolean
  open import Data.Boolean.Stmt
  open import Data.Either as Either using (_‖_)
  open import Functional
  open import Logic
  open import Logic.Classical
  open import Type.Dependent
  open import Type.Dependent.Functions
  open import Syntax.Function

  -- TODO: Many of these operations are simply copy-pasted from Sets.IterativeSet with small modifications.

  -- The operation converting an IUset from a lower universe level to a higher universe level.
  IUset-level-up : IUset(T){ℓ₁} → IUset(T){ℓ₁ Lvl.⊔ ℓ₂}
  IUset-level-up          (atom x) = atom x
  IUset-level-up {ℓ₁}{ℓ₂} (setc {Index} elem) = setc {Lvl.Up{ℓ₁}{ℓ₂}(Index)} \{(Lvl.up i) → IUset-level-up{ℓ₁}{ℓ₂}(elem(i))}

  -- The empty set, consisting of no elements.
  -- Index is the empty type, which means that there are no objects pointing to elements in the set.
  ∅ : IUset(T){ℓ}
  ∅ = setc empty

  -- Lifts an unary operation on set containers to an unary operation on IUsets.
  set-operator₁ : (SetContainer(T){ℓ₁} → SetContainer(T){ℓ₂}) → (IUset(T){ℓ₁} → IUset(T){ℓ₂})
  set-operator₁ op (atom _) = ∅
  set-operator₁ op (set  A) = set (op A)

  -- Lifts a binary operation on set containers to a binary operation on IUsets.
  set-operator₂ : (SetContainer(T){ℓ} → SetContainer(T){ℓ} → SetContainer(T){ℓ}) → (IUset(T){ℓ} → IUset(T){ℓ} → IUset(T){ℓ})
  set-operator₂ op (atom _) (atom _) = ∅
  set-operator₂ op (atom _) (set  B) = set B
  set-operator₂ op (set  A) (atom _) = set A
  set-operator₂ op (set  A) (set  B) = set (op A B)

  -- Filters a set to only contain set elements.
  sets-of : IUset(T){ℓ} → IUset(T){ℓ}
  sets-of{ℓ} = set-operator₁(A ↦ intro (Σ(SetContainer.Index(A)) (ia ↦ LvlConvert(IsSet(SetContainer.elem(A)(ia))){ℓ})) \{(intro ia p) → SetContainer.elem(A)(ia)})

  -- Filters a set to only contain atomic elements.
  atoms-of : IUset(T){ℓ} → IUset(T){ℓ}
  atoms-of{ℓ} = set-operator₁(A ↦ intro (Σ(SetContainer.Index(A)) (ia ↦ LvlConvert(IsAtom(SetContainer.elem(A)(ia))){ℓ})) \{(intro ia p) → SetContainer.elem(A)(ia)})

  -- The singleton set, consisting of one element.
  -- Index is the unit type, which means that there are a single object pointing to a single element in the set.
  singleton : IUset(T){ℓ} → IUset(T){ℓ}
  singleton = setc{Index = Unit} ∘ const

  -- The pair set, consisting of two elements.
  -- Index is the boolean type, which means that there are two objects pointing to two elements in the set.
  pair : IUset(T){ℓ} → IUset(T){ℓ} → IUset(T){ℓ}
  pair A B = setc{Index = Lvl.Up(Bool)} \{(Lvl.up 𝐹) → A ; (Lvl.up 𝑇) → B}

  -- The union operator.
  -- Index(A ∪ B) is the either type of two indices, which means that both objects from the A and the B index point to elements in the set.
  _∪_ : IUset(T){ℓ} → IUset(T){ℓ} → IUset(T){ℓ}
  A ∪ B = setc{Index = Index(A) ‖ Index(B)} (Either.map1 (elem(A)) (elem(B)))
  -- _∪_ = set-operator₂([ℰ]-map₂ Either.map1)

  -- The big union operator.
  -- Index(⋃ A) is the dependent sum type of an Index(A) and the index of the element this index points to.
  ⋃ : IUset(T){ℓ} → IUset(T){ℓ}
  ⋃ A = setc{Index = Σ(Index(A)) (ia ↦ Index(elem(A)(ia)))} (\{(intro ia i) → elem(elem(A)(ia))(i)})

  indexFilter : (A : IUset(T){ℓ}) → (Index(A) → Stmt{ℓ}) → IUset(T){ℓ}
  indexFilter A P = setc{Index = Σ(Index(A)) P} (elem(A) ∘ Σ.left)

  filter : (A : IUset(T){ℓ}) → (IUset(T){ℓ} → Stmt{ℓ}) → IUset(T){ℓ}
  filter{ℓ} A P = indexFilter A (P ∘ elem(A))

  indexFilterBool : (A : IUset(T){ℓ}) → (Index(A) → Bool) → IUset(T){ℓ}
  indexFilterBool A f = indexFilter A (Lvl.Up ∘ IsTrue ∘ f)

  filterBool : (A : IUset(T){ℓ}) → (IUset(T){ℓ} → Bool) → IUset(T){ℓ}
  filterBool A f = indexFilterBool A (f ∘ elem(A))

  map : (IUset(T){ℓ} → IUset(T){ℓ}) → (IUset(T){ℓ} → IUset(T){ℓ})
  map f(A) = setc{Index = Index(A)} (f ∘ elem(A))

  -- The power set operator.
  -- Index(℘(A)) is a function type. An instance of such a function represents a subset, and essentially maps every element in A to a boolean which is interpreted as "in the subset of not".
  -- Note: This only works properly in a classical setting. Trying to use indexFilter instead result in universe level problems.
  ℘ : IUset(T){ℓ} → IUset(T){ℓ}
  ℘(A) = setc{Index = Index(A) → Bool} (indexFilterBool A)

  -- The set of ordinal numbers of the first order.
  ω : IUset(T){ℓ}
  ω = setc{Index = Lvl.Up ℕ} (N ∘ Lvl.Up.obj) where
    open import Numeral.Natural
    N : ℕ → IUset(T){ℓ}
    N(𝟎)    = ∅
    N(𝐒(n)) = N(n) ∪ singleton(N(n))

  module Proofs where
    open import Data.Boolean
    open import Data.Tuple as Tuple using ()
    open import Logic.Propositional
    open import Logic.Predicate
    open import Structure.Function
    open import Structure.Relator.Properties

    instance
      atom-function : Function(atom{T = T}{ℓ})
      Function.congruence atom-function = atom

    {-instance
      set-function : Function(set{T = T}{ℓ})
      Function.congruence set-function = ?
    -}

    -- If there is an element in the empty set, then there exists an instance of the empty type by definition, and that is false by definition.
    ∅-membership : ∀{x : IUset(T){ℓ₁}} → (x ∉ ∅ {ℓ₂})
    ∅-membership (set())

    -- There is a bijection between (A ‖ B) and ∃{Lvl.Up Bool}(\{(Lvl.up 𝐹) → A ; (Lvl.up 𝑇) → B}).
    pair-membership : ∀{a b x : IUset(T){ℓ}} → (x ∈ pair a b) ↔ (x ≡ a)∨(x ≡ b)
    Tuple.left (pair-membership {x = x}) ([∨]-introₗ p) = set ([∃]-intro (Lvl.up 𝐹) ⦃ p ⦄)
    Tuple.left (pair-membership {x = x}) ([∨]-introᵣ p) = set ([∃]-intro (Lvl.up 𝑇) ⦃ p ⦄)
    Tuple.right pair-membership (set ([∃]-intro (Lvl.up 𝐹) ⦃ atom p ⦄)) = [∨]-introₗ (atom p)
    Tuple.right pair-membership (set ([∃]-intro (Lvl.up 𝑇) ⦃ atom p ⦄)) = [∨]-introᵣ (atom p)
    Tuple.right pair-membership (set ([∃]-intro (Lvl.up 𝐹) ⦃ set l r ⦄)) = [∨]-introₗ (set l r)
    Tuple.right pair-membership (set ([∃]-intro (Lvl.up 𝑇) ⦃ set l r ⦄)) = [∨]-introᵣ (set l r)

    -- There is a bijection between (A) and ∃{Unit}(\{<> → A}).
    singleton-membership : ∀{a x : IUset(T){ℓ}} → (x ∈ singleton(a)) ↔ (x ≡ a)
    Tuple.left singleton-membership xin = set ([∃]-intro <> ⦃ xin ⦄)
    Tuple.right singleton-membership (set ([∃]-intro _ ⦃ eq ⦄)) = eq

    [∪]-membership : ∀{A B x : IUset(T){ℓ}} → (x ∈ (A ∪ B)) ↔ (x ∈ A)∨(x ∈ B)
    Tuple.left [∪]-membership ([∨]-introₗ (set ([∃]-intro ia))) = set ([∃]-intro (Either.Left  ia))
    Tuple.left [∪]-membership ([∨]-introᵣ (set ([∃]-intro ib))) = set ([∃]-intro (Either.Right ib))
    Tuple.right ([∪]-membership {A = set x}) (set ([∃]-intro ([∨]-introₗ ia))) = [∨]-introₗ (set ([∃]-intro ia))
    Tuple.right ([∪]-membership {B = set x}) (set ([∃]-intro ([∨]-introᵣ ib))) = [∨]-introᵣ (set ([∃]-intro ib))

    [⊆]-with-elem : ∀{SCₗ SCᵣ : SetContainer(T){ℓ}} → (xy : set SCₗ ⊆ set SCᵣ) → ∀{ix} → (elem (set SCₗ) ix ≡ elem (set SCᵣ) ([⊆]-map xy ix))
    [⊆]-with-elem (set map proof) {ix} = proof{ix}

    open import Lang.Inspect
    import      Relator.Equals as Equals
    import      Relator.Equals.Proofs.Equivalence as Equals
    [⋃]-membership : ∀{A x : IUset(T){ℓ}} → (x ∈ (⋃ A)) ↔ ∃(a ↦ (a ∈ A) ∧ (x ∈ a))
    Tuple.left ([⋃]-membership {A = A@(set _)}) ([∃]-intro a@(set _) ⦃ [∧]-intro aA xa ⦄) with elem A ([∈]-index aA) | [∈]-elem aA | inspect ⦃ Equals.[≡]-equiv ⦄ (elem A) ([∈]-index aA)
    ... | set _ | (set aA-mapₗ aA-mapᵣ) | intro pp = set ([∃]-intro (intro ([∈]-index aA) (Equals.[≡]-substitutionₗ pp {f = Index} ([⊆]-map aA-mapᵣ ([∈]-index xa)))) ⦃ [≡]-transitivity-raw ([∈]-elem xa) ([⊆]-with-elem ([≡]-to-[⊆] ([≡]-transitivity-raw ([∈]-elem aA) ([≡]-transitivity-raw (sub₂(Equals._≡_)(_≡_) pp) {!!}))) {[∈]-index xa}) ⦄)
    Tuple.right ([⋃]-membership {A = A@(atom _)}) (set ([∃]-intro (intro iA ia))) = {!!}
    ∃.witness (Tuple.right ([⋃]-membership {A = A@(set _)}) (set ([∃]-intro (intro iA ia)))) = elem(A) iA
    ∃.proof (Tuple.right ([⋃]-membership {A = A@(set _)}) (set ([∃]-intro (intro iA ia) ⦃ proof ⦄))) = [∧]-intro ([∈]-of-elem {A = A}) {!set([∃]-intro ia ⦃ proof ⦄)!}

{-  Σ.left  (∃.witness (Tuple.left ([⋃]-membership {A = A} {x}) ([∃]-intro a ⦃ [∧]-intro ([∃]-intro iA) _ ⦄))) = iA
  Σ.right (∃.witness (Tuple.left ([⋃]-membership {A = A} {x}) ([∃]-intro a ⦃ [∧]-intro ([∃]-intro iA ⦃ aA ⦄) ([∃]-intro ia) ⦄))) = _⊆_.map (_≡_.right aA) ia

  ∃.proof (Tuple.left ([⋃]-membership {A = A} {x}) ([∃]-intro a ⦃ [∧]-intro ([∃]-intro iA ⦃ aA ⦄) ([∃]-intro ia ⦃ xa ⦄) ⦄)) = [≡]-transitivity-raw xa ([⊆]-with-elem (sub₂(_≡_)(_⊆_) aA) {ia})

  ∃.witness (Tuple.right ([⋃]-membership {A = A} {x}) ([∃]-intro (intro iA ia) ⦃ proof ⦄)) = elem(A)(iA)
  Tuple.left (∃.proof (Tuple.right ([⋃]-membership {A = A} {x}) ([∃]-intro (intro iA ia) ⦃ proof ⦄))) = [∈]-of-elem {A = A}
  ∃.witness (Tuple.right (∃.proof (Tuple.right ([⋃]-membership {A = A} {x}) ([∃]-intro (intro iA ia) ⦃ proof ⦄)))) = ia
  ∃.proof (Tuple.right (∃.proof (Tuple.right ([⋃]-membership {A = A} {x}) ([∃]-intro (intro iA ia) ⦃ proof ⦄)))) = proof
-}
