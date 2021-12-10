module Data.List.Equiv.Id where

import Lvl
open import Functional
open import Function.Names as Names using (_⊜_)
import      Function.Equals as Fn
open import Data.Boolean
open import Data.Option
open import Data.Option.Equiv.Id
open import Data.Option.Proofs using ()
open import Data.List
open import Data.List.Equiv
open import Data.List.Functions
open import Logic
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Relator.Equals
open import Structure.Function
open import Structure.Function.Domain
import      Structure.Function.Names as Names
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Setoid using (Equiv) renaming (_≡_ to _≡ₛ_)
open import Syntax.Implication
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ ℓₑₗ ℓₑₒ ℓₑ₁ ℓₑ₂ ℓₑₗ₁ ℓₑₗ₂ : Lvl.Level
private variable T A B : Type{ℓ}
private variable n : ℕ

open import Relator.Equals
open import Relator.Equals.Proofs

private variable l l₁ l₂ : List(T)
private variable a b x : T
private variable f : A → B
private variable P : List(T) → Stmt{ℓ}

[⊰]-general-cancellation : ((a ⊰ l₁) ≡ (b ⊰ l₂)) → (a ≡ b) ∧ (l₁ ≡ l₂)
[⊰]-general-cancellation p = [∧]-intro (L p) (R p) where
  R : ((a ⊰ l₁) ≡ (b ⊰ l₂)) → (l₁ ≡ l₂)
  R p = congruence₁(tail) p

  L : ((a ⊰ l₁) ≡ (b ⊰ l₂)) → (a ≡ b)
  L {l₁ = ∅}     {l₂ = ∅}      [≡]-intro = [≡]-intro
  L {l₁ = ∅}     {l₂ = _ ⊰ _} p with () ← R p
  L {l₁ = _ ⊰ _} {l₂ = _ ⊰ _} p = injective(Some) (congruence₁(first) p)

instance
  List-Id-extensionality : Extensionality([≡]-equiv {T = List(T)})
  Extensionality.generalized-cancellationᵣ List-Id-extensionality = [∧]-elimₗ ∘ [⊰]-general-cancellation
  Extensionality.generalized-cancellationₗ List-Id-extensionality = [∧]-elimᵣ ∘ [⊰]-general-cancellation
  Extensionality.case-unequality           List-Id-extensionality ()

open import Data.List.Proofs

initial-0-length : (initial(0)(l) ≡ ∅)
initial-0-length {l = ∅}     = reflexivity(_≡_)
initial-0-length {l = x ⊰ l} = reflexivity(_≡_)
{-# REWRITE initial-0-length #-}

multiply-singleton-repeat : (singleton(l) ++^ n ≡ repeat(l)(n))
multiply-singleton-repeat {l = l} {n = 𝟎}   = reflexivity(_≡_)
multiply-singleton-repeat {l = l} {n = 𝐒 n} = congruence₁(l ⊰_) (multiply-singleton-repeat {l = l} {n = n})

module _ {f g : A → B} where
  map-function-raw : (f ⊜ g) → (map f ⊜ map g)
  map-function-raw p {∅} = reflexivity(_≡_)
  map-function-raw p {x ⊰ l} rewrite p{x} = congruence₁(g(x) ⊰_) (map-function-raw p {l})

module _ {f g : A → List(B)} where
  concatMap-function-raw : (f ⊜ g) → (concatMap f ⊜ concatMap g)
  concatMap-function-raw p {∅}                  = reflexivity(_≡_)
  concatMap-function-raw p {x ⊰ l} rewrite p{x} = congruence₁(g(x) ++_) (concatMap-function-raw p {l})

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type{ℓ₁}} {B : Type{ℓ₂}} {C : Type{ℓ₃}} {f : B → C}{g : A → B} where
  map-preserves-[∘] : (map(f ∘ g) ⊜ (map f ∘ map g))
  map-preserves-[∘] {x = ∅}     = reflexivity(_≡_)
  map-preserves-[∘] {x = x ⊰ l} = congruence₁(f(g(x)) ⊰_) (map-preserves-[∘] {x = l})

map-preserves-id : (map id ⊜ id{T = List(T)})
map-preserves-id {x = ∅} = reflexivity(_≡_)
map-preserves-id {x = x ⊰ l} = congruence₁(x ⊰_) (map-preserves-id {x = l})
{-# REWRITE map-preserves-id #-}

concatMap-[++] : (concatMap f (l₁ ++ l₂) ≡ (concatMap f l₁ ++ concatMap f l₂))
concatMap-[++] {f = f} {∅}      {l₂} = reflexivity(_≡_)
concatMap-[++] {f = f} {x ⊰ l₁} {l₂} =
  (f(x) ++ concatMap f (l₁ ++ l₂))             🝖-[ congruence₁(f(x) ++_) (concatMap-[++] {f = f} {l₁} {l₂}) ]
  (f(x) ++ (concatMap f l₁ ++ concatMap f l₂)) 🝖-[ associativity(_++_) {x = f(x)}{y = concatMap f l₁}{z = concatMap f l₂} ]-sym
  (f(x) ++ concatMap f l₁ ++ concatMap f l₂)   🝖-end

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type{ℓ₁}} {B : Type{ℓ₂}} {C : Type{ℓ₃}} {f : B → List(C)}{g : A → List(B)} where
  concatMap-[∘] : (concatMap(concatMap f ∘ g)) ⊜ (concatMap f ∘ concatMap g)
  concatMap-[∘] {∅}     = reflexivity(_≡_)
  concatMap-[∘] {x ⊰ l} =
    (concatMap(concatMap f ∘ g)) (x ⊰ l)                  🝖[ _≡_ ]-[]
    (concatMap f ∘ g) x ++ concatMap(concatMap f ∘ g) l   🝖-[ congruence₁((concatMap f ∘ g) x ++_) (concatMap-[∘] {l}) ]
    (concatMap f ∘ g) x ++ (concatMap f ∘ concatMap g) l  🝖[ _≡_ ]-[]
    (concatMap f (g(x))) ++ (concatMap f (concatMap g l)) 🝖-[ concatMap-[++] {f = f}{l₁ = g(x)}{l₂ = concatMap g l} ]-sym
    concatMap f (g(x) ++ concatMap g l)                   🝖[ _≡_ ]-[]
    concatMap f (concatMap g (x ⊰ l))                     🝖[ _≡_ ]-[]
    (concatMap f ∘ concatMap g) (x ⊰ l)                   🝖-end

concatMap-singleton : (concatMap{A = T} singleton) ⊜ id
concatMap-singleton {x = ∅} = reflexivity(_≡_)
concatMap-singleton {x = x ⊰ l} = congruence₁(x ⊰_) (concatMap-singleton {x = l})

concatMap-concat-map : (concatMap f l ≡ concat(map f l))
concatMap-concat-map        {l = ∅} = reflexivity(_≡_)
concatMap-concat-map {f = f}{l = x ⊰ l} =
  concatMap f (x ⊰ l)     🝖[ _≡_ ]-[]
  f(x) ++ concatMap f l   🝖[ _≡_ ]-[ congruence₂-₂(_++_)(f(x)) (concatMap-concat-map {l = l}) ]
  f(x) ++ concat(map f l) 🝖[ _≡_ ]-[]
  concat(f(x) ⊰ map f l)  🝖[ _≡_ ]-[]
  concat(map f (x ⊰ l))   🝖-end

foldₗ-lastElem-equivalence : (last{T = T} ⊜ foldₗ (const Option.Some) Option.None)
foldₗ-lastElem-equivalence {x = ∅}         = reflexivity(_≡_)
foldₗ-lastElem-equivalence {x = x ⊰ ∅}     = reflexivity(_≡_)
foldₗ-lastElem-equivalence {x = x ⊰ y ⊰ l} = foldₗ-lastElem-equivalence {x = y ⊰ l}

{-
foldₗ-reverse-equivalence : (reverse{T = T} ⊜ foldₗ (Functional.swap(_⊰_)) ∅)
foldₗ-reverse-equivalence {x = ∅} = reflexivity(_≡_)
foldₗ-reverse-equivalence {x = x ⊰ l} =
  reverse (x ⊰ l)                                           🝖[ _≡_ ]-[]
  (postpend x ∘ reverse) l                                  🝖[ _≡_ ]-[ congruence₁(postpend x) (foldₗ-reverse-equivalence {x = l}) ]
  (postpend x ∘ foldₗ (Functional.swap(_⊰_)) ∅) l           🝖[ _≡_ ]-[ {!!} ]
  foldₗ (Functional.swap(_⊰_)) (Functional.swap(_⊰_) ∅ x) l 🝖[ _≡_ ]-[]
  foldₗ (Functional.swap(_⊰_)) (singleton(x)) l             🝖[ _≡_ ]-[]
  foldₗ (Functional.swap(_⊰_)) ∅ (x ⊰ l)                    🝖-end
-}

foldᵣ-function : ⦃ equiv : Equiv{ℓₑ}(B) ⦄ → ∀{_▫_ : A → B → B} ⦃ oper : BinaryOperator(_▫_) ⦄ → Function ⦃ equiv-B = equiv ⦄ (foldᵣ(_▫_) a)
foldᵣ-function {a = a} ⦃ equiv ⦄ {_▫_ = _▫_} ⦃ oper ⦄ = intro p where
  p : Names.Congruence₁ ⦃ equiv-B = equiv ⦄ (foldᵣ(_▫_) a)
  p {∅}       {∅}       xy = reflexivity(Equiv._≡_ equiv)
  p {x₁ ⊰ l₁} {x₂ ⊰ l₂} xy =
    foldᵣ(_▫_) a (x₁ ⊰ l₁) 🝖[ Equiv._≡_ equiv ]-[]
    x₁ ▫ (foldᵣ(_▫_) a l₁) 🝖[ Equiv._≡_ equiv ]-[ congruence₂(_▫_) ⦃ oper ⦄ ([∧]-elimₗ([⊰]-general-cancellation xy)) (p {l₁} {l₂} ([∧]-elimᵣ([⊰]-general-cancellation xy))) ]
    x₂ ▫ (foldᵣ(_▫_) a l₂) 🝖[ Equiv._≡_ equiv ]-[]
    foldᵣ(_▫_) a (x₂ ⊰ l₂) 🝖-end

foldᵣ-function₊-raw : ∀{l₁ l₂ : List(A)} ⦃ equiv : Equiv{ℓₑ}(B) ⦄ {_▫₁_ _▫₂_ : A → B → B} ⦃ oper₁ : BinaryOperator(_▫₁_) ⦄ ⦃ oper₂ : BinaryOperator ⦃ [≡]-equiv ⦄ ⦃ equiv ⦄ ⦃ equiv ⦄ (_▫₂_) ⦄ {a₁ a₂ : B} → (∀{x y} → (_≡ₛ_ ⦃ equiv ⦄ (x ▫₁ y) (x ▫₂ y))) → (_≡ₛ_ ⦃ equiv ⦄ a₁ a₂) → (l₁ ≡ l₂) → (foldᵣ(_▫₁_) a₁ l₁ ≡ₛ foldᵣ(_▫₂_) a₂ l₂)
foldᵣ-function₊-raw {l₁ = ∅} {∅} ⦃ equiv ⦄ {_▫₁_} {_▫₂_} ⦃ oper₁ ⦄ ⦃ oper₂ ⦄ {a₁} {a₂} opeq aeq leq = aeq
foldᵣ-function₊-raw {l₁ = x₁ ⊰ l₁} {x₂ ⊰ l₂} ⦃ equiv ⦄ {_▫₁_} {_▫₂_} ⦃ oper₁ ⦄ ⦃ oper₂ ⦄ {a₁} {a₂} opeq aeq leq =
  foldᵣ(_▫₁_) a₁ (x₁ ⊰ l₁)  🝖[ Equiv._≡_ equiv ]-[]
  x₁ ▫₁ (foldᵣ(_▫₁_) a₁ l₁) 🝖[ Equiv._≡_ equiv ]-[ congruence₂(_▫₁_) ⦃ oper₁ ⦄ ([∧]-elimₗ([⊰]-general-cancellation leq)) (foldᵣ-function₊-raw {l₁ = l₁} {l₂} ⦃ equiv ⦄ {_▫₁_}{_▫₂_} ⦃ oper₁ ⦄ ⦃ oper₂ ⦄ {a₁}{a₂} opeq aeq ([∧]-elimᵣ([⊰]-general-cancellation leq))) ]
  x₂ ▫₁ (foldᵣ(_▫₂_) a₂ l₂) 🝖[ Equiv._≡_ equiv ]-[ opeq{x₂}{foldᵣ(_▫₂_) a₂ l₂} ]
  x₂ ▫₂ (foldᵣ(_▫₂_) a₂ l₂) 🝖[ Equiv._≡_ equiv ]-[]
  foldᵣ(_▫₂_) a₂ (x₂ ⊰ l₂)  🝖[ Equiv._≡_ equiv ]-end

map-binaryOperator : BinaryOperator {A₁ = A → B} ⦃ equiv-A₁ = Fn.[⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄ ⦃ equiv-A₂ = [≡]-equiv ⦄ (map)
map-binaryOperator = intro p where
  p : Names.Congruence₂(map)
  p {f} {g} {∅}       {∅}       fg xy = reflexivity(_≡_)
  p {f} {g} {x₁ ⊰ l₁} {x₂ ⊰ l₂} fg xy =
    • (
      f(x₁) 🝖[ _≡_ ]-[ Fn._⊜_.proof fg {x₁} ]
      g(x₁) 🝖[ _≡_ ]-[ congruence₁(g) ([∧]-elimₗ([⊰]-general-cancellation xy)) ]
      g(x₂) 🝖-end
    )
    • (
      map f(l₁) 🝖[ _≡_ ]-[ p fg ([∧]-elimᵣ([⊰]-general-cancellation xy)) ]
      map g(l₂) 🝖-end
    )
    ⇒₂-[ congruence₂(_⊰_) ]
    (f(x₁) ⊰ map f(l₁) ≡ g(x₂) ⊰ map g(l₂)) ⇒-end

count-of-[++] : ∀{P} → (count P (l₁ ++ l₂) ≡ count P l₁ + count P l₂)
count-of-[++] {l₁ = ∅}       {l₂ = l₂} {P = P} = reflexivity(_≡_)
count-of-[++] {l₁ = x₁ ⊰ l₁} {l₂ = l₂} {P = P} with P(x₁) | count-of-[++] {l₁ = l₁} {l₂ = l₂} {P = P}
... | 𝑇 | p = congruence₁ 𝐒(p)
... | 𝐹 | p = p

-- TODO Is this true?: count-single-equality-equivalence : (∀{P} → count P l₁ ≡ count P l₂) ↔ (∀{x} → (count (x ≡?_) l₁ ≡ count (x ≡?_) l₂))

foldᵣ-preserves-[++] : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}}{_▫₁_ : A → B → B}{_▫₂_ : B → B → B}{id} ⦃ ident : Identityₗ(_▫₂_)(id) ⦄ {a b} → (Names.AssociativityPattern(_▫₁_)(_▫₂_)(_▫₁_)(_▫₂_)) → (foldᵣ(_▫₁_) id (a ++ b) ≡ (foldᵣ(_▫₁_) id a) ▫₂ (foldᵣ(_▫₁_) id b))
foldᵣ-preserves-[++] {_▫₁_ = _▫₁_}{_▫₂_ = _▫₂_}{id} {∅}      {b} p =
  foldᵣ(_▫₁_) id (∅ ++ b)                 🝖[ _≡_ ]-[]
  foldᵣ(_▫₁_) id b                        🝖[ _≡_ ]-[ identityₗ(_▫₂_)(id) ]-sym
  id ▫₂ foldᵣ(_▫₁_) id b                  🝖[ _≡_ ]-[]
  (foldᵣ(_▫₁_) id ∅) ▫₂ (foldᵣ _▫₁_ id b) 🝖-end
foldᵣ-preserves-[++] {_▫₁_ = _▫₁_}{_▫₂_ = _▫₂_}{id} {a ⊰ al} {b} p =
  foldᵣ(_▫₁_) id (a ⊰ (al ++ b))                   🝖[ _≡_ ]-[]
  a ▫₁ (foldᵣ(_▫₁_) id (al ++ b))                  🝖[ _≡_ ]-[ congruence₂-₂(_▫₁_)(a) (foldᵣ-preserves-[++] {_▫₁_ = _▫₁_} {_▫₂_ = _▫₂_} {id} {al} {b} p) ]
  a ▫₁ ((foldᵣ(_▫₁_) id al) ▫₂ (foldᵣ(_▫₁_) id b)) 🝖[ _≡_ ]-[ p ]-sym
  (a ▫₁ (foldᵣ(_▫₁_) id al)) ▫₂ (foldᵣ(_▫₁_) id b) 🝖[ _≡_ ]-[]
  (foldᵣ(_▫₁_) id (a ⊰ al)) ▫₂ (foldᵣ(_▫₁_) id b)  🝖-end

foldᵣ-preserves-[++]-by-assoc : ∀{ℓ}{T : Type{ℓ}}{_▫_ : T → T → T} ⦃ assoc : Associativity(_▫_) ⦄ {id} ⦃ ident : Identityₗ(_▫_)(id) ⦄ {a b : List(T)} → (foldᵣ(_▫_) id (a ++ b) ≡ (foldᵣ(_▫_) id a) ▫ (foldᵣ(_▫_) id b))
foldᵣ-preserves-[++]-by-assoc {_▫_ = _▫_} {id} {a}{b} = foldᵣ-preserves-[++] {_▫₁_ = _▫_}{_▫₂_ = _▫_}{id} {a}{b} (associativity(_▫_))
