module Sets.ImageSet.Oper where

open import Data
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
open import Sets.ImageSet
open import Structure.Function
open import Structure.Setoid.WithLvl renaming (_≡_ to _≡ₛ_)
open import Type
open import Type.Dependent

private variable ℓ ℓₑ ℓᵢ ℓᵢ₁ ℓᵢ₂ ℓᵢ₃ ℓᵢₑ ℓ₁ ℓ₂ ℓ₃ : Lvl.Level
private variable T X Y Z : Type{ℓ}

module _ where
  open import Data.Boolean
  open import Data.Boolean.Stmt
  open import Data.Either as Either using (_‖_)
  open import Function.Domains

  ∅ : ImageSet{ℓᵢ}(T)
  ∅ = intro empty

  𝐔 : ImageSet{Lvl.of(T)}(T)
  𝐔 = intro id

  singleton : T → ImageSet{ℓᵢ}(T)
  singleton(x) = intro{Index = Unit} \{<> → x}

  pair : T → T → ImageSet{ℓᵢ}(T)
  pair x y = intro{Index = Lvl.Up(Bool)} \{(Lvl.up 𝐹) → x ; (Lvl.up 𝑇) → y}

  _∪_ : ImageSet{ℓᵢ₁}(T) → ImageSet{ℓᵢ₂}(T) → ImageSet{ℓᵢ₁ Lvl.⊔ ℓᵢ₂}(T)
  A ∪ B = intro{Index = Index(A) ‖ Index(B)} (Either.map1 (elem(A)) (elem(B)))

  ⋃ : ImageSet{ℓᵢ}(ImageSet{ℓᵢ}(T)) → ImageSet{ℓᵢ}(T)
  ⋃ A = intro{Index = Σ(Index(A)) (Index ∘ elem(A))} \{(intro ia i) → elem(elem(A)(ia))(i)}

  indexFilter : (A : ImageSet{ℓᵢ}(T)) → (Index(A) → Stmt{ℓ}) → ImageSet{ℓᵢ Lvl.⊔ ℓ}(T)
  indexFilter A P = intro {Index = Σ(Index(A)) P} (elem(A) ∘ Σ.left)

  filter : (T → Stmt{ℓ}) → ImageSet{ℓᵢ}(T) → ImageSet{ℓᵢ Lvl.⊔ ℓ}(T)
  filter P(A) = indexFilter A (P ∘ elem(A))

  indexFilterBool : (A : ImageSet{ℓᵢ}(T)) → (Index(A) → Bool) → ImageSet{ℓᵢ}(T)
  indexFilterBool A f = indexFilter A (IsTrue ∘ f)

  filterBool : (T → Bool) → ImageSet{ℓᵢ}(T) → ImageSet{ℓᵢ}(T)
  filterBool f(A) = indexFilterBool A (f ∘ elem(A))

  map : (X → Y) → (ImageSet{ℓᵢ}(X) → ImageSet{ℓᵢ}(Y))
  map f(A) = intro{Index = Index(A)} (f ∘ elem(A))

  unapply : (X → Y) → ⦃ _ : Equiv{ℓₑ}(Y)⦄ → (Y → ImageSet{Lvl.of(X) Lvl.⊔ ℓₑ}(X))
  unapply f(y) = intro{Index = ∃(x ↦ f(x) ≡ₛ y)} [∃]-witness

  -- unmap : (X → Y) → ⦃ _ : Equiv{ℓₑ}(Y)⦄ → (ImageSet{{!Lvl.of(T) Lvl.⊔ ℓₑ!}}(Y) → ImageSet{Lvl.of(T) Lvl.⊔ ℓₑ}(X))
  -- unmap f(B) = intro{Index = ∃(x ↦ f(x) ∈ B)} [∃]-witness

  ℘ : ImageSet{ℓᵢ}(T) → ImageSet{Lvl.𝐒(ℓᵢ)}(ImageSet{ℓᵢ}(T))
  ℘(A) = intro{Index = Index(A) → Stmt} (indexFilter A)

  _∩_ : ⦃ _ : Equiv{ℓᵢ}(T) ⦄ → ImageSet{ℓᵢ}(T) → ImageSet{ℓᵢ}(T) → ImageSet{ℓᵢ}(T)
  A ∩ B = indexFilter(A) (iA ↦ elem(A) iA ∈ B)

  ⋂ : ⦃ _ : Equiv{ℓᵢ}(T) ⦄ → ImageSet{Lvl.of(T)}(ImageSet{Lvl.of(T)}(T)) → ImageSet{ℓᵢ Lvl.⊔ Lvl.of(T)}(T)
  -- ⋂ As = intro{Index = Σ((iAs : Index(As)) → Index(elem(As) iAs)) (f ↦ (∀{iAs₁ iAs₂} → (elem(elem(As) iAs₁)(f iAs₁) ≡ₛ elem(elem(As) iAs₂)(f iAs₂))))} {!!} (TODO: I think this definition only works with excluded middle because one must determine if an A from AS is empty or not and if it is not, then one can apply its index to the function in the Σ)
  ⋂ As = indexFilter(⋃ As) (iUAs ↦ ∃{Obj = (iAs : Index(As)) → Index(elem(As) iAs)}(f ↦ ∀{iAs} → (elem(⋃ As) iUAs ≡ₛ elem(elem(As) iAs) (f iAs))))
  -- ⋂ As = indexFilter(⋃ As) (iUAs ↦ ∀{iAs} → (elem(⋃ As) iUAs ∈ elem(As) iAs))

  {-
module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  open import Data.Boolean
  open import Data.Either as Either using (_‖_)
  open import Data.Tuple as Tuple using (_⨯_ ; _,_)
  import      Structure.Container.SetLike as Sets
  open import Structure.Function.Domain
  open import Structure.Operator.Properties
  open import Structure.Relator
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  private variable A B C : ImageSet{ℓₑ}(T)
  private variable x y a b : T

  [∈]-of-elem : ∀{ia : Index(A)} → (elem(A)(ia) ∈ A)
  ∃.witness ([∈]-of-elem {ia = ia}) = ia
  ∃.proof    [∈]-of-elem = reflexivity(_≡ₛ_)

  instance
    ∅-membership : Sets.EmptySet(_∈_ {T = T}{ℓ})
    Sets.EmptySet.∅          ∅-membership = ∅
    Sets.EmptySet.membership ∅-membership ()

  instance
    𝐔-membership : Sets.UniversalSet(_∈_ {T = T})
    Sets.UniversalSet.𝐔          𝐔-membership = 𝐔
    Sets.UniversalSet.membership 𝐔-membership {x = x} = [∃]-intro x ⦃ reflexivity(_≡ₛ_) ⦄

  instance
    singleton-membership : Sets.SingletonSet(_∈_ {T = T}{ℓ})
    Sets.SingletonSet.singleton singleton-membership = singleton
    Sets.SingletonSet.membership singleton-membership = proof where
      proof : (x ∈ singleton{ℓᵢ = ℓᵢ}(a)) ↔ (x ≡ₛ a)
      Tuple.left  proof xin = [∃]-intro <> ⦃ xin ⦄
      Tuple.right proof ([∃]-intro i ⦃ eq ⦄ ) = eq

  instance
    pair-membership : Sets.PairSet(_∈_ {T = T}{ℓ})
    Sets.PairSet.pair pair-membership = pair
    Sets.PairSet.membership pair-membership = proof where
      proof : (x ∈ pair a b) ↔ (x ≡ₛ a)∨(x ≡ₛ b)
      Tuple.left  proof ([∨]-introₗ p) = [∃]-intro (Lvl.up 𝐹) ⦃ p ⦄
      Tuple.left  proof ([∨]-introᵣ p) = [∃]-intro (Lvl.up 𝑇) ⦃ p ⦄
      Tuple.right proof ([∃]-intro (Lvl.up 𝐹) ⦃ eq ⦄) = [∨]-introₗ eq
      Tuple.right proof ([∃]-intro (Lvl.up 𝑇) ⦃ eq ⦄) = [∨]-introᵣ eq

  instance
    [∪]-membership : Sets.UnionOperator(_∈_ {T = T})
    Sets.UnionOperator._∪_        [∪]-membership = _∪_
    Sets.UnionOperator.membership [∪]-membership = proof where
      proof : (x ∈ (A ∪ B)) ↔ (x ∈ A)∨(x ∈ B)
      Tuple.left  proof ([∨]-introₗ ([∃]-intro  ia)) = [∃]-intro (Either.Left  ia)
      Tuple.left  proof ([∨]-introᵣ ([∃]-intro  ib)) = [∃]-intro (Either.Right ib)
      Tuple.right proof ([∃]-intro  ([∨]-introₗ ia)) = [∨]-introₗ ([∃]-intro ia)
      Tuple.right proof ([∃]-intro  ([∨]-introᵣ ib)) = [∨]-introᵣ ([∃]-intro ib)

  instance
    [∩]-membership : Sets.IntersectionOperator(_∈_ {T = T})
    Sets.IntersectionOperator._∩_        [∩]-membership = _∩_
    Sets.IntersectionOperator.membership [∩]-membership = proof where
      proof : (x ∈ (A ∩ B)) ↔ (x ∈ A)∧(x ∈ B)
      _⨯_.left proof ([↔]-intro ([∃]-intro iA ⦃ pA ⦄) ([∃]-intro iB ⦃ pB ⦄)) = [∃]-intro (intro iA ([∃]-intro iB ⦃ symmetry(_≡ₛ_) pA 🝖 pB ⦄))
      _⨯_.right proof ([∃]-intro (intro iA ([∃]-intro iB ⦃ pAB ⦄)) ⦃ pxAB ⦄) = [∧]-intro ([∃]-intro iA) ([∃]-intro iB ⦃ pxAB 🝖 pAB ⦄)

  instance
    map-membership : Sets.MapFunction(_∈_ {T = T})(_∈_ {T = T})
    Sets.MapFunction.map        map-membership f = map f
    Sets.MapFunction.membership map-membership {f = f} ⦃ function ⦄ = proof where
      proof : (y ∈ map f(A)) ↔ ∃(x ↦ (x ∈ A) ∧ (f(x) ≡ₛ y))
      ∃.witness (Tuple.left  (proof)                         ([∃]-intro x ⦃ [∧]-intro xA fxy ⦄)) = [∃]-witness xA
      ∃.proof   (Tuple.left  (proof {y = y} {A = A}) ([∃]-intro x ⦃ [∧]-intro xA fxy ⦄)) =
        y                                🝖[ _≡ₛ_ ]-[ fxy ]-sym
        f(x)                             🝖[ _≡ₛ_ ]-[ congruence₁(f) ⦃ function ⦄ ([∃]-proof xA) ]
        f(elem(A) ([∃]-witness xA))      🝖[ _≡ₛ_ ]-[]
        elem (map f(A)) ([∃]-witness xA) 🝖[ _≡ₛ_ ]-end
      ∃.witness (Tuple.right (proof {A = A}) ([∃]-intro iA))       = elem(A) iA
      ∃.proof   (Tuple.right proof           ([∃]-intro iA ⦃ p ⦄)) = [∧]-intro ([∈]-of-elem {ia = iA}) (symmetry(_≡ₛ_) p)

  indexFilter-membership : ∀{P : Index(A) → Stmt{ℓ}} → (x ∈ indexFilter A P) ↔ ∃(i ↦ (x ≡ₛ elem(A) i) ∧ P(i))
  _⨯_.left indexFilter-membership ([∃]-intro iA ⦃ [∧]-intro xe p ⦄) = [∃]-intro (intro iA p) ⦃ xe ⦄
  _⨯_.right indexFilter-membership ([∃]-intro (intro iA p) ⦃ xe ⦄) = [∃]-intro iA ⦃ [∧]-intro xe p ⦄

  indexFilter-subset : ∀{P : Index(A) → Stmt{ℓₑ}} → (indexFilter{ℓₑ} A P ⊆ A)
  indexFilter-subset = [∃]-map-proof [∧]-elimₗ ∘ [↔]-to-[→] indexFilter-membership

  indexFilter-elem-membershipₗ : ∀{P : Index(A) → Stmt{ℓ}}{i : Index(A)} → (elem(A)(i) ∈ indexFilter A P) ← P(i)
  indexFilter-elem-membershipₗ {i = i} pi = [∃]-intro (intro i pi) ⦃ reflexivity _ ⦄

  indexFilter-elem-membershipᵣ : ⦃ _ : Equiv{ℓₑ}(Index(A)) ⦄ ⦃ _ : Injective(elem A) ⦄ → ∀{P : Index(A) → Stmt{ℓ}} ⦃ _ : UnaryRelator(P) ⦄{i : Index(A)} → (elem(A)(i) ∈ indexFilter A P) → P(i)
  indexFilter-elem-membershipᵣ {A = A}{P = P} {i = i} ([∃]-intro (intro iA PiA) ⦃ p ⦄) = substitute₁ₗ(P) (injective(elem A) p) PiA

  instance
    filter-membership : Sets.FilterFunction(_∈_ {T = T})
    Sets.FilterFunction.filter     filter-membership f       = filter{ℓ = ℓₑ} f
    Sets.FilterFunction.membership filter-membership {P = P} = proof where
      proof : (x ∈ filter P(A)) ↔ ((x ∈ A) ∧ P(x))
      Tuple.left proof ([∧]-intro ([∃]-intro i ⦃ p ⦄) pb) = [∃]-intro (intro i (substitute₁(P) p pb)) ⦃ p ⦄
      Tuple.left  (Tuple.right proof ([∃]-intro (intro iA PiA)))        = [∃]-intro iA
      Tuple.right (Tuple.right proof ([∃]-intro (intro iA PiA) ⦃ pp ⦄)) = substitute₁ₗ(P) pp PiA

  filter-subset : ∀{P : T → Stmt{ℓₑ}} → (filter P(A) ⊆ A)
  filter-subset ([∃]-intro (intro i p) ⦃ xf ⦄) = [∃]-intro i ⦃ xf ⦄

  instance
    postulate [∩]-commutativity : Commutativity(_∩_ {T = T})

  -- TODO: These should come from Structure.Container.SetLike, which in turn should come from Structure.Operator.Lattice, which in turn should come from Structure.Relator.Ordering.Lattice
  postulate [∩]-subset-of-right : (A ⊆ B) → (A ∩ B ≡ₛ B)
  postulate [∩]-subset-of-left : (B ⊆ A) → (A ∩ B ≡ₛ A)
  postulate [∩]-subsetₗ : (A ∩ B) ⊆ A
  [∩]-subsetᵣ : (A ∩ B) ⊆ B
  [∩]-subsetᵣ {A} {B} {x} xAB = indexFilter-subset ([↔]-to-[→] (commutativity(_∩_) ⦃ [∩]-commutativity ⦄ {A} {B} {x}) xAB)

  instance
    ℘-membership : Sets.PowerFunction(_∈_)(_∈_)
    Sets.PowerFunction.℘ ℘-membership = ℘
    Sets.PowerFunction.membership ℘-membership = [↔]-intro l r where
      l : (B ∈ ℘(A)) ← (B ⊆ A)
      ∃.witness (l {B} {A} BA) iA = elem(A) iA ∈ B
      _⨯_.left (∃.proof (l {B}{A} BA) {x}) a = apply a $
        A ∩ B 🝖[ _⊆_ ]-[ [∩]-subsetᵣ ]
        B     🝖[ _⊆_ ]-end
      _⨯_.right (∃.proof (l {B}{A} BA) {x}) b = apply b $
        B     🝖[ _⊆_ ]-[ BA ]
        A     🝖[ _⊆_ ]-[ sub₂(_≡_)(_⊇_) ([∩]-subset-of-left BA) ]
        A ∩ B 🝖[ _⊆_ ]-end

      r : (B ∈ ℘(A)) → (B ⊆ A)
      r ([∃]-intro _ ⦃ BA ⦄) xB with [↔]-to-[→] BA xB
      ... | [∃]-intro (intro iA _) ⦃ xe ⦄ = [∃]-intro iA ⦃ xe ⦄
-}
