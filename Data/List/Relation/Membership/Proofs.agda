module Data.List.Relation.Membership.Proofs where

import Lvl
open import Functional
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.List
open import Data.List.Equiv
open import Data.List.Functions hiding (skip)
open import Data.List.Relation.Membership
open import Data.List.Relation.Quantification hiding (use ; skip)
open import Data.List.Relation.Quantification.Proofs
import      Data.Tuple as Tuple
open import Logic
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.Natural
open import Structure.Function
open import Structure.Relator
open import Structure.Relator.Proofs
open import Structure.Relator.Properties
open import Structure.Setoid renaming (_≡_ to _≡ₛ_)
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ : Lvl.Level
private variable T A B C : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  private variable l l₁ l₂ : List(T)
  private variable ll : List(List(T))
  private variable a b c x : T

  instance
    [∈]-relatorₗ : UnaryRelator(_∈ l)
    [∈]-relatorₗ = UnaryRelator-introᵣ p where
      p : Names.Substitution₁ᵣ(_∈ l)
      p{x ⊰ _}     xy (• q) = • (symmetry(_≡ₛ_) xy 🝖 q)
      p{x ⊰ y ⊰ l} xy (⊰ q) = ⊰ p{y ⊰ l} xy q

  [∈]-self : AllElements(_∈ l)(l)
  [∈]-self {∅}     = ∅
  [∈]-self {x ⊰ l} = (• reflexivity(_≡ₛ_)) ⊰ AllElements-fn (⊰_) ([∈]-self {l})

  [∉]-empty : (a ∉ ∅)
  [∉]-empty ()

  [∈]-in-singleton : (a ∈ singleton(a))
  [∈]-in-singleton = use(reflexivity(_≡ₛ_))

  [∈]-singleton : (a ∈ singleton(b)) ↔ (a ≡ₛ b)
  [∈]-singleton = [↔]-intro L R where
    L : (a ∈ singleton(b)) ← (a ≡ₛ b)
    L p = substitute₁ᵣ(_∈ _) (symmetry(_≡ₛ_) p) [∈]-in-singleton

    R : (a ∈ singleton(b)) → (a ≡ₛ b)
    R(use p) = p
    R(skip ())

  [∈][++] : (a ∈ (l₁ ++ l₂)) ↔ ((a ∈ l₁) ∨ (a ∈ l₂))
  [∈][++] = [↔]-intro L R where
    L : (a ∈ (l₁ ++ l₂)) ← ((a ∈ l₁) ∨ (a ∈ l₂))
    L {l₁ = ∅}      ([∨]-introᵣ p)     = p
    L {l₁ = x ⊰ l₁} ([∨]-introₗ (• p)) = • p
    L {l₁ = x ⊰ l₁} ([∨]-introₗ (⊰ p)) = ⊰ L {l₁ = l₁} ([∨]-introₗ p)
    L {l₁ = x ⊰ l₁} ([∨]-introᵣ p)     = ⊰ L {l₁ = l₁} ([∨]-introᵣ p)

    R : (a ∈ (l₁ ++ l₂)) → ((a ∈ l₁) ∨ (a ∈ l₂))
    R {l₁ = ∅}      p     = [∨]-introᵣ p
    R {l₁ = x ⊰ l₁} (• p) = [∨]-introₗ (• p)
    R {l₁ = x ⊰ l₁} (⊰ p) with R {l₁ = l₁} p
    ... | [∨]-introₗ q = [∨]-introₗ (⊰ q)
    ... | [∨]-introᵣ q = [∨]-introᵣ q

  [∈]-postpend : (a ∈ postpend a l)
  [∈]-postpend{l = ∅}     = use (reflexivity(_≡ₛ_))
  [∈]-postpend{l = _ ⊰ l} = skip([∈]-postpend{l = l})

  open import Data
  open import Data.Boolean.Stmt.Logic
  open import Lang.Inspect
  open import Relator.Equals using() renaming (_≡_ to _≡ₑ_)
  open import Relator.Equals.Proofs.Equivalence
  [∈]-filter : ∀{f} ⦃ func : Function ⦃ equiv-B = [≡]-equiv ⦄ (f) ⦄ → (a ∈ filter f(l)) ↔ ((a ∈ l) ∧ IsTrue(f(a)))
  [∈]-filter{l = ll}{f = f} = [↔]-intro (Tuple.uncurry L) (x ↦ [∧]-intro (R₁ x) (R₂{l = ll} x)) where
    instance _ = [≡]-equiv {T = Bool}

    L : (a ∈ l) → IsTrue(f(a)) → (a ∈ filter f(l))
    L{a}{x ⊰ l} p fa with f(x) | inspect f(x)
    L{a}{x ⊰ l} (• p) fa | 𝑇 | _        = • p
    L{a}{x ⊰ l} (⊰ p) fa | 𝑇 | _        = ⊰ L {a} {l} p fa
    L{a}{x ⊰ l} (• p) fa | 𝐹 | intro fx with () ← disjointness (substitute₁ᵣ(IsTrue) ⦃ [≡]-unaryRelator ⦄ (congruence₁(f) p) fa) ([↔]-to-[←] IsFalse.is-𝐹 fx)
    L{a}{x ⊰ l} (⊰ p) fa | 𝐹 | intro _  = L {a} {l} p fa

    R₁ : (a ∈ filter f(l)) → (a ∈ l)
    R₁{l = x ⊰ l} p with f(x)
    R₁{l = x ⊰ l} (• p) | 𝑇 = • p
    R₁{l = x ⊰ l} (⊰ p) | 𝑇 = ⊰ R₁{l = l} p
    R₁{l = x ⊰ l} p     | 𝐹 = ⊰ R₁{l = l} p
    
    R₂ : (a ∈ filter f(l)) → IsTrue(f(a))
    R₂{a}{x ⊰ l} p with f(a) | inspect f(a)
    R₂{a}{x ⊰ l} p     | 𝑇 | _ = <>
    R₂{a}{x ⊰ l} p     | 𝐹 | _ with f(x) | inspect f(x)
    R₂{a}{x ⊰ l} (• p) | 𝐹 | intro fa | 𝑇 | intro fx with () ← symmetry(_≡ₑ_) fa 🝖 congruence₁(f) p 🝖 fx
    R₂{a}{x ⊰ l} (⊰ p) | 𝐹 | intro fa | 𝑇 | intro fx with () ← disjointness ([↔]-to-[←] IsFalse.is-𝐹 fa) (R₂{a}{l} p)
    R₂{a}{x ⊰ l} p     | 𝐹 | intro fa | 𝐹 | intro fx with () ← disjointness ([↔]-to-[←] IsFalse.is-𝐹 fa) (R₂{a}{l} p)

module _ ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
  private variable f : A → B
  private variable l l₁ l₂ : List(T)
  private variable a b c x : T

  [∈]-mapᵣ : ⦃ func-f : Function(f) ⦄ → (a ∈ l) → (f(a) ∈ (map f(l)))
  [∈]-mapᵣ {f = f} (use p)  = use (congruence₁(f) p)
  [∈]-mapᵣ         (skip p) = skip([∈]-mapᵣ p)

  [∈]-mapₗ : ⦃ func-f : Function(f) ⦄ → ∃(a ↦ (b ≡ₛ f(a)) ∧ (a ∈ l)) ← (b ∈ map f(l))
  [∈]-mapₗ {l = a ⊰ l} (• p) = [∃]-intro a ⦃ [∧]-intro p (• reflexivity(_≡ₛ_)) ⦄
  [∈]-mapₗ {l = a ⊰ l} (⊰ p) = [∃]-map-proof ([∧]-map id (⊰_)) ([∈]-mapₗ p)

  [∈]-map : ⦃ func-f : Function(f) ⦄ → ∃(a ↦ (b ≡ₛ f(a)) ∧ (a ∈ l)) ↔ (b ∈ map f(l))
  [∈]-map {f = f}{l = l} = [↔]-intro [∈]-mapₗ \([∃]-intro a ⦃ [∧]-intro eq al ⦄) → substitute₁ᵣ(_∈ map f(l)) (symmetry(_≡ₛ_) eq) ([∈]-mapᵣ al)

module _ ⦃ equiv : Equiv{ℓₑ₁}(T) ⦄ ⦃ equiv-List : Equiv{ℓₑ₂}(List(T)) ⦄ ⦃ ext : Extensionality(equiv-List) ⦄ where
  private variable l l₁ l₂ : List(T)
  private variable ll : List(List(T))
  private variable a b c x : T
  private variable f : A → B

  instance
    [∈]-relatorᵣ : UnaryRelator(x ∈_)
    [∈]-relatorᵣ {x} = UnaryRelator-introᵣ p where
      p : Names.Substitution₁ᵣ(x ∈_)
      p {x₁ ⊰ l₁} {∅}       eq mem with () ← [∅][⊰]-unequal (symmetry(Equiv._≡_ equiv-List) eq)
      p {x₁ ⊰ l₁} {x₂ ⊰ l₂} eq (• mem) = • (mem 🝖 [⊰]-generalized-cancellationᵣ eq)
      p {x₁ ⊰ l₁} {x₂ ⊰ l₂} eq (⊰ mem) = ⊰ p{l₁}{l₂} ([⊰]-generalized-cancellationₗ eq) mem

  instance
    [∈]-relator : BinaryRelator(_∈_)
    [∈]-relator = BinaryRelator-unary-intro [∈]-relatorₗ [∈]-relatorᵣ

  [∈]-concat : (x ∈ concat ll) ↔ ∃(l ↦ (l ∈ ll) ∧ (x ∈ l))
  [∈]-concat = [↔]-intro L R where
    L : (x ∈ concat ll) ← ∃(l ↦ (l ∈ ll) ∧ (x ∈ l))
    L {x}{ll = ll0 ⊰ ll} ([∃]-intro l ⦃ [∧]-intro (• lll) xl ⦄) = [↔]-to-[←] ([∈][++] {a = x}{ll0}{concat ll}) ([∨]-introₗ (substitute₂-₂ᵣ(_∈_)(x) lll xl))
    L {x}{ll = ll0 ⊰ ll} ([∃]-intro l ⦃ [∧]-intro (⊰ lll) xl ⦄) = [↔]-to-[←] ([∈][++] {a = x}{ll0}{concat ll}) ([∨]-introᵣ (L{ll = ll} ([∃]-intro l ⦃ [∧]-intro lll xl ⦄)))

    R : (x ∈ concat ll) → ∃(l ↦ (l ∈ ll) ∧ (x ∈ l))
    R {x} {l ⊰ ll} p with [↔]-to-[→] ([∈][++] {a = x}{l}{concat ll}) p
    ... | [∨]-introₗ xl = [∃]-intro l ⦃ [∧]-intro (• reflexivity(_≡ₛ_)) xl ⦄
    ... | [∨]-introᵣ xl
      with [∃]-intro l2 ⦃ [∧]-intro l₁ll xl₁ ⦄ ← R{x}{ll} xl
      = [∃]-intro l2 ⦃ [∧]-intro (⊰ l₁ll) xl₁ ⦄

module _ ⦃ equiv₁ : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv₂ : Equiv{ℓₑ₂}(B) ⦄ ⦃ equiv-List : Equiv{ℓₑ₃}(List(B)) ⦄ ⦃ ext : Extensionality(equiv-List) ⦄ where
  private variable l : List(A)
  private variable x : B
  private variable f : A → List(B)

  open import Data.List.Equiv.Id
  open import Logic.Propositional.Theorems
  [∈]-concatMap : ⦃ func : Function(f) ⦄ → (x ∈ concatMap f(l)) ↔ ∃(y ↦ (y ∈ l) ∧ (x ∈ f(y)))
  [∈]-concatMap{f}{x}{l}
    rewrite concatMap-concat-map{f = f}{l}
    = [↔]-transitivity
      ([∈]-concat {x = x}{map f(l)})
      ([↔]-intro
        (\([∃]-intro y ⦃ [∧]-intro p q ⦄) → [∃]-intro (f(y)) ⦃ [∧]-intro ([∈]-mapᵣ p) q ⦄)
        (\([∃]-intro y ⦃ [∧]-intro p q ⦄) →
          let ([∃]-intro z ⦃ [∧]-intro r s ⦄) = [∈]-mapₗ {f = f}{l = l} p
          in [∃]-intro z ⦃ [∧]-intro s (substitute₁ᵣ(x ∈_) r q) ⦄
        )
      )

module _ where
  open import Data.List.Relation.Permutation
  open import Data.List.Relation.Permutation.Proofs  
  open import Relator.Equals.Proofs.Equiv

  private variable l : List(T)
  private variable x : T

  [∈]-relatorᵣ-by-permutation : UnaryRelator ⦃ permutes-equiv ⦄ (x ∈_)
  [∈]-relatorᵣ-by-permutation {x = x} = UnaryRelator-introᵣ ⦃ permutes-equiv ⦄ p where
      p : Names.Substitution₁ᵣ ⦃ permutes-equiv ⦄ (x ∈_)
      p (prepend perm)      (• xl)     = • xl
      p (prepend perm)      (⊰ xl)     = ⊰ p perm xl
      p _permutes_.swap     (• xl)     = ⊰ (• xl)
      p _permutes_.swap     (⊰ (• xl)) = • xl
      p _permutes_.swap     (⊰ (⊰ xl)) = ⊰ (⊰ xl)
      p (trans perm₁ perm₂) xl         = p perm₂ (p perm₁ xl)

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  open import Data.List.Relation.Sublist
  open import Data.List.Relation.Sublist.Proofs

  private variable l l₁ l₂ : List(T)
  private variable ll : List(List(T))
  private variable a b c x : T

  [⊑]-to-[∈] : (l₁ ⊑ l₂) → (∀{x} → (x ∈ l₁) → (x ∈ l₂))
  [⊑]-to-[∈] (_⊑_.use eq sub) (• xin) = • (xin 🝖 eq)
  [⊑]-to-[∈] (_⊑_.use eq sub) (⊰ xin) = ⊰ [⊑]-to-[∈] sub xin
  [⊑]-to-[∈] (_⊑_.skip sub)   xin     = ⊰ [⊑]-to-[∈] sub xin

  AllElements-[∈] : ∀{P : _ → Type{ℓ}} ⦃ rel : UnaryRelator(P) ⦄ → AllElements P(l) ↔ (∀{x} → (x ∈ l) → P(x))
  AllElements-[∈] {P = P} = [↔]-intro L R where
    L : AllElements P(l) ← (∀{x} → (x ∈ l) → P(x))
    L{∅}     p = ∅
    L{x ⊰ l} p = p(• reflexivity(_≡ₛ_)) ⊰ L{l} (p ∘ ⊰_)

    R : AllElements P(l) → (∀{x} → (x ∈ l) → P(x))
    R (px ⊰ pl) (• elem) = substitute₁ₗ(P) elem px
    R (px ⊰ pl) (⊰ elem) = R pl elem

{- TODO: Stuff below is supposed to be moved to Structure.Sets.Proofs

[∈][++]-expandₗ : (a ∈ l₂) → (a ∈ (l₁ ++ l₂))
[∈][++]-expandₗ {l₂ = l₂}{l₁ = l₁} = [↔]-to-[←] ([∈][++] {l₁ = l₁}{l₂ = l₂}) ∘ [∨]-introᵣ

[∈][++]-expandᵣ : (a ∈ l₁) → (a ∈ (l₁ ++ l₂))
[∈][++]-expandᵣ {l₁ = l₁}{l₂ = l₂} = [↔]-to-[←] ([∈][++] {l₁ = l₁}{l₂ = l₂}) ∘ [∨]-introₗ

[∈][⊰]-reorderₗ : (a ∈ (l₁ ++ (x ⊰ l₂))) → (a ∈ (x ⊰ (l₁ ++ l₂)))
[∈][⊰]-reorderₗ (a∈l₁++xl₂) = [∨]-elim left right ([↔]-to-[→] [∈]-[++] (a∈l₁++xl₂)) where
  left : (a ∈ l₁) → (a ∈ (x ⊰ (l₁ ++ l₂)))
  left (a∈l₁) = [∈][⊰]-expand ([∈][++]-expandᵣ {a}{l₁}{l₂} (a∈l₁))

  right : ∀{a} → (a ∈ (x ⊰ l₂)) → (a ∈ (x ⊰ (l₁ ++ l₂)))
  {-right ([∈]-id)              = use
  right ([∈][⊰]-expand (a∈l₂)) = [∈][⊰]-expand ([∈][++]-expandₗ {_}{l₁}{l₂} (a∈l₂))-}

-- [∈][⊰]-reorderᵣ : ∀{a x}{l₁ l₂} → (a ∈ (x ⊰ (l₁ ++ l₂))) → (a ∈ (l₁ ++ (x ⊰ l₂)))
-- [∈][⊰]-reorderᵣ {a}{x}{l₁}{l₂} ([∈]-id) = 
-- [∈][⊰]-reorderᵣ {a}{x}{l₁}{l₂} ([∈][⊰]-expand (a∈l₁++l₂)) = 

[∈]-in-middle : (a ∈ (l₁ ++ singleton(a) ++ l₂))
[∈]-in-middle{a}{l₁}{l₂} = [↔]-to-[←] ([∈]-[++] {a}{l₁ ++ singleton(a)}{l₂}) ([∨]-introₗ ([∈]-at-last{l = l₁}))

module _ where
  private variable ℓ₂ : Lvl.Level

  [⊆]-substitution : ∀{l₁ l₂ : List(T)} → (l₁ ⊆ l₂) → ∀{P : T → Stmt{ℓ₂}} → (∀{a} → (a ∈ l₂) → P(a)) → (∀{a} → (a ∈ l₁) → P(a))
  [⊆]-substitution (l₁⊆l₂) proof = proof ∘ (l₁⊆l₂)

  [⊇]-substitution : ∀{l₁ l₂ : List(T)} → (l₁ ⊇ l₂) → ∀{P : T → Stmt{ℓ₂}} → (∀{a} → (a ∈ l₁) → P(a)) → (∀{a} → (a ∈ l₂) → P(a))
  [⊇]-substitution (l₁⊇l₂) proof = proof ∘ (l₁⊇l₂)

  [≡]-substitutionₗ : ∀{l₁ l₂ : List(T)} → (l₁ ≡ l₂) → ∀{P : T → Stmt{ℓ₂}} → (∀{a} → (a ∈ l₁) → P(a)) → (∀{a} → (a ∈ l₂) → P(a))
  [≡]-substitutionₗ (l₁≡l₂) = [⊆]-substitution ([↔]-to-[←] (l₁≡l₂))

  [≡]-substitutionᵣ : ∀{l₁ l₂ : List(T)} → (l₁ ≡ l₂) → ∀{P : T → Stmt{ℓ₂}} → (∀{a} → (a ∈ l₂) → P(a)) → (∀{a} → (a ∈ l₁) → P(a))
  [≡]-substitutionᵣ (l₁≡l₂) = [⊆]-substitution ([↔]-to-[→] (l₁≡l₂))
-}

{-
open import Structure.Relator.Properties

instance
  [⊆]-reflexivity : Reflexivity(_⊆_)
  Reflexivity.proof [⊆]-reflexivity = id

instance
  [⊆]-antisymmetry : Antisymmetry(_⊆_)(_≡_)
  Antisymmetry.proof [⊆]-antisymmetry = swap [↔]-intro

instance
  [⊆]-transitivity : Transitivity(_⊆_)
  Transitivity.proof [⊆]-transitivity xy yz = yz ∘ xy

instance
  [⊆]-reflexivity : Reflexivity(_⊆_)

[≡]-reflexivity : ∀{L} → (L ≡ L)
-- [≡]-reflexivity = [↔]-intro [⊆]-reflexivity [⊆]-reflexivity


[≡]-symmetry : ∀{l₁ l₂} → (l₁ ≡ l₂) → (l₂ ≡ l₁)
[≡]-symmetry (l₁≡l₂) {x} with (l₁≡l₂){x}
... | [↔]-intro l r = [↔]-intro r l


[≡]-transitivity : ∀{l₁ l₂ L₃} → (l₁ ≡ l₂) → (l₂ ≡ L₃) → (l₁ ≡ L₃)
[≡]-transitivity (l₁≡l₂) (l₂≡L₃) {x} with [∧]-intro ((l₁≡l₂){x}) ((l₂≡L₃){x})
... | ([∧]-intro (lr₁) (lr₂)) = [↔]-transitivity  (lr₁) (lr₂)

-- [⊆]-application : ∀{l₁ l₂} → (l₁ ⊆ l₂) → ∀{f} → (map f(l₁))⊆(map f(l₂))
-- [⊆]-application proof fl₁ = [∈]-proof.application ∘ proof
-- (∀{x} → (x ∈ l₂) → (x ∈ l₁)) → ∀{f} → (∀{x} → (x ∈ map f(l₂)) → (x ∈ map f(l₁)))

{-
[≡]-included-in : ∀{L : List(T)}{x} → (x ∈ L) → ((x ⊰ L) ≡ L)
[≡]-included-in xL = [⊆]-antisymmetry (sub xL) (super xL) where
  super : ∀{L : List(T)}{x} → (x ∈ L) → ((x ⊰ L) ⊇ L)
  super [∈]-id  [∈]-id  = [∈]-id
  super [∈]-id  (skip p) = skip ?
  super (skip p) [∈]-id  = skip(use ?)
  super (skip p ) (skip q) = skip(skip ?)

  sub : ∀{L : List(T)}{x} → (x ∈ L) → ((x ⊰ L) ⊆ L)
  sub use  use          = use
  sub use  (skip ⦃ p ⦄) = p
  sub skip use          = skip
  sub skip (skip ⦃ p ⦄) = p
-}

postulate [≡]-included-subset : ∀{l₁ l₂ : List(T)} → (l₁ ⊆ l₂) → ((l₁ ++ l₂) ≡ l₂)

postulate [≡]-subset-[++] : ∀{L l₁ l₂ : List(T)} → (l₁ ⊆ L) → (l₂ ⊆ L) → (l₁ ++ l₂ ⊆ L)


[⊆]-with-[⊰] : ∀{l₁ l₂ : List(T)} → (l₁ ⊆ l₂) → ∀{b} → (l₁ ⊆ (b ⊰ l₂))
[⊆]-with-[⊰] (l₁⊆l₂) (x∈l₁) = [∈][⊰]-expand ((l₁⊆l₂) (x∈l₁))


[⊆]-with-[++]ₗ : ∀{l₁ l₂ : List(T)} → (l₁ ⊆ l₂) → ∀{L₃} → (l₁ ⊆ (L₃ ++ l₂))
-- [⊆]-with-[++]ₗ {l₁}{l₂} (l₁⊆l₂) {L₃} (x∈l₁) = [∈][++]-expandₗ {_}{L₃}{l₂} ((l₁⊆l₂) (x∈l₁))


[⊆]-with-[++]ᵣ : ∀{l₁ l₂ : List(T)} → (l₁ ⊆ l₂) → ∀{L₃} → (l₁ ⊆ (l₂ ++ L₃))
[⊆]-with-[++]ᵣ {l₁}{l₂} (l₁⊆l₂) {L₃} (x∈l₁) = [∈][++]-expandᵣ {_}{l₂}{L₃} ((l₁⊆l₂) (x∈l₁))

-- TODO: Does this work? It would be easier to "port" all (∈)-theorems to (⊆)-theorems then.
-- [∈]-to-[⊆]-property : ∀{l₂}{f : List(T) → List(T)} → (∀{a} → (a ∈ l₂) → (a ∈ f(l₂))) → (∀{l₁} → (l₁ ⊆ l₂) → (l₁ ⊆ f(l₂)))

-}

module _ where
  open import Relator.Equals as Id
  open import Relator.Equals.Proofs.Equiv

  non-empty-inclusion-existence : ∀{l : List(T)} → (l Id.≢ ∅) → ∃(_∈ l)
  non-empty-inclusion-existence {l = ∅}     p with () ← p(reflexivity(Id._≡_))
  non-empty-inclusion-existence {l = x ⊰ l} p = [∃]-intro x ⦃ •(reflexivity(Id._≡_)) ⦄
