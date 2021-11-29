module Data.List.Proofs where

import Lvl
open import Functional as Fn using (_∘_ ; const)
open import Data.Option using (Option ; Some ; None)
import      Data.Option.Functions as Option
open import Data.List
open import Data.List.Equiv
open import Data.List.Functions
open import Logic
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Relator.Equals renaming (_≡_ to _≡ₑ_ ; _≢_ to _≢ₑ_)
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Multi
import      Structure.Function.Names as Names
import      Structure.Operator.Names as Names
open import Structure.Operator.Proofs.Util
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ ℓₑₗ ℓₑₒ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑₗ₁ ℓₑₗ₂ ℓₑₗ₃ : Lvl.Level
private variable T A B C D : Type{ℓ}
private variable n : ℕ

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ equiv-List : Equiv{ℓₑₗ}(List(T)) ⦄ ⦃ extensionality : Extensionality(equiv-List) ⦄ where
  private variable l l₁ l₂ : List(T)
  private variable a b x : T
  private variable P : List(T) → Stmt{ℓ}

  open Equiv(equiv-List) using () renaming (_≡_ to _≡ₗ_)

  instance
    tail-function : Function(tail)
    Function.congruence tail-function {∅}      {∅}      p = p
    Function.congruence tail-function {∅}      {x ⊰ y}  p with () ← [∅][⊰]-unequal p
    Function.congruence tail-function {x ⊰ xl} {∅}      p with () ← [∅][⊰]-unequal (symmetry(_≡_) p)
    Function.congruence tail-function {x ⊰ xl} {y ⊰ yl} p = [⊰]-generalized-cancellationₗ p

  instance
    first-function : ⦃ equiv-Option : Equiv{ℓₑₒ}(Option(T)) ⦄ ⦃ Some-function : Function(Some) ⦄ → Function(first)
    Function.congruence first-function {∅}      {∅}      p = reflexivity(_≡_)
    Function.congruence first-function {∅}      {y ⊰ yl} p with () ← [∅][⊰]-unequal p
    Function.congruence first-function {x ⊰ xl} {∅}      p with () ← [∅][⊰]-unequal (symmetry(_≡_) p)
    Function.congruence first-function {x ⊰ xl} {y ⊰ yl} p = congruence₁(Some) ([⊰]-generalized-cancellationᵣ p)

  instance
    [⊰]-cancellationₗ : Cancellationₗ(_⊰_)
    Cancellationₗ.proof([⊰]-cancellationₗ) = [⊰]-generalized-cancellationₗ

  instance
    [⊰]-cancellationᵣ : Cancellationᵣ(_⊰_)
    Cancellationᵣ.proof([⊰]-cancellationᵣ) = [⊰]-generalized-cancellationᵣ

  [⊰]-unequal : (x ⊰ l ≢ l)
  [⊰]-unequal {l = ∅} = [∅][⊰]-unequal ∘ symmetry(_≡_)
  [⊰]-unequal {l = x ⊰ l} = [⊰]-unequal {l = l} ∘ [⊰]-generalized-cancellationₗ

  postpend-of-prepend : (postpend a (b ⊰ l) ≡ b ⊰ postpend a l)
  postpend-of-prepend = reflexivity(_≡_)

  instance
    postpend-function : BinaryOperator(postpend)
    postpend-function = intro p where
      p : Names.Congruence₂(postpend)
      p {x₂ = ∅}        {y₂ = ∅}        px pl = congruence₂(_⊰_) px pl
      p {x₂ = ∅}        {y₂ = y₂ ⊰ yl₂} px pl with () ← [∅][⊰]-unequal pl
      p {x₂ = x₂ ⊰ xl₂} {y₂ = ∅}        px pl with () ← [∅][⊰]-unequal (symmetry(_≡_) pl)
      p {x₂ = x₂ ⊰ xl₂} {y₂ = y₂ ⊰ yl₂} px pl = congruence₂(_⊰_) ([⊰]-generalized-cancellationᵣ pl) (p{x₂ = xl₂} {y₂ = yl₂} px ([⊰]-generalized-cancellationₗ pl))

  instance
    reverse-function : Function(reverse)
    reverse-function = intro p where
      p : Names.Congruence₁(reverse)
      p {∅}      {∅}      pl = reflexivity(_≡_)
      p {∅}      {y ⊰ yl} pl with () ← [∅][⊰]-unequal pl
      p {x ⊰ xl} {∅}      pl with () ← [∅][⊰]-unequal (symmetry(_≡_) pl)
      p {x ⊰ xl} {y ⊰ yl} pl = congruence₂(postpend) ([⊰]-generalized-cancellationᵣ pl) (p([⊰]-generalized-cancellationₗ pl))

  instance
    [++]-identityₗ : Identityₗ(_++_) ∅
    Identityₗ.proof([++]-identityₗ) = reflexivity(_≡_)

  instance
    [++]-identityᵣ : Identityᵣ(_++_) ∅
    Identityᵣ.proof([++]-identityᵣ) {x = l} = elim (reflexivity(_≡_)) (\x l → congruence₂ᵣ(_⊰_)(x) {l ++ ∅}{l}) l

  instance
    [++]-associativity : Associativity(_++_)
    Associativity.proof([++]-associativity) {l₁}{l₂}{l₃} = elim (reflexivity(_≡_)) (\x l → congruence₂ᵣ(_⊰_)(x) {(l ++ l₂) ++ l₃}{l ++ (l₂ ++ l₃)}) l₁

  reverse-postpend : (reverse(postpend a l) ≡ a ⊰ reverse l)
  reverse-postpend {a = a}{l = l} = elim (reflexivity(_≡ₗ_)) (\x l p → congruence₂ᵣ(postpend) ⦃ postpend-function ⦄ (x) {reverse(postpend a l)}{a ⊰ reverse l} p) l

  prepend-[++] : (a ⊰ l ≡ singleton{T = T}(a) ++ l)
  prepend-[++] = reflexivity(_≡_)

  postpend-[++] : (postpend{T = T} a l ≡ l ++ singleton(a))
  postpend-[++] {a = a}{l = l} = elim (reflexivity(_≡_)) (\x l → congruence₂ᵣ(_⊰_)(x) {postpend a l}{l ++ (singleton a)}) l

  postpend-of-[++] : (postpend{T = T} a (l₁ ++ l₂) ≡ l₁ ++ postpend a l₂)
  postpend-of-[++] {a = a} {l₁}{l₂} = elim (reflexivity(_≡_)) (\x l → congruence₂ᵣ(_⊰_)(x) {postpend a (l ++ l₂)}{l ++ (postpend a l₂)}) l₁

  reverse-[++] : (reverse(l₁ ++ l₂) ≡ reverse(l₂) ++ reverse(l₁))
  reverse-[++] {l₁ = l₁} {l₂ = l₂} = elim
    (congruence₁(reverse) (identityₗ(_++_)(∅) {l₂}) 🝖 symmetry(_≡_) (identityᵣ(_++_)(∅) {reverse l₂}))
    (\x l₁ p → congruence₂ᵣ(postpend) ⦃ postpend-function ⦄ (x) {reverse (l₁ ++ l₂)}{reverse l₂ ++ reverse l₁} p 🝖 postpend-of-[++] {l₁ = reverse l₂} {l₂ = reverse l₁})
    l₁

  [∅]-postpend-unequal : (postpend x l ≢ ∅)
  [∅]-postpend-unequal {l = ∅}     = [∅][⊰]-unequal ∘ symmetry(_≡_)
  [∅]-postpend-unequal {l = _ ⊰ l} = [∅][⊰]-unequal ∘ symmetry(_≡_)

  postpend-unequal : (postpend x l ≢ l)
  postpend-unequal {l = ∅}     = [∅][⊰]-unequal ∘ symmetry(_≡_)
  postpend-unequal {l = y ⊰ l} = postpend-unequal {l = l} ∘ cancellationₗ(_⊰_)

  [++]-middle-prepend-postpend : postpend x l₁ ++ l₂ ≡ l₁ ++ (x ⊰ l₂)
  [++]-middle-prepend-postpend {l₁ = ∅}      {l₂ = ∅} = reflexivity(_≡_)
  [++]-middle-prepend-postpend {l₁ = ∅}      {l₂ = x ⊰ l₂} = reflexivity(_≡_)
  [++]-middle-prepend-postpend {l₁ = x ⊰ l₁} {l₂ = l₂} = congruence₂ᵣ(_⊰_)(x) ([++]-middle-prepend-postpend {l₁ = l₁} {l₂ = l₂})

  instance
    [++]-cancellationₗ : Cancellationₗ(_++_)
    Cancellationₗ.proof [++]-cancellationₗ {x}{y}{z} = proof {x}{y}{z} where
      proof : Names.Cancellationₗ (_++_)
      proof {∅}     p = p
      proof {x ⊰ l} p = proof {l} (cancellationₗ(_⊰_) p)

  instance
    [++]-cancellationᵣ : Cancellationᵣ(_++_)
    Cancellationᵣ.proof([++]-cancellationᵣ) {a}{b} = proof {a}{b} where
      proof : Names.Cancellationᵣ(_++_)
      proof {z}      {∅}      {∅}      p = reflexivity(_≡_)
      proof {z}      {x ⊰ xl} {y ⊰ yl} p = congruence₂(_⊰_) ([⊰]-generalized-cancellationᵣ p) (proof {z}{xl}{yl} ([⊰]-generalized-cancellationₗ p))
      proof {∅}      {∅}      {y ⊰ yl} p with () ← [∅][⊰]-unequal {l = yl} (p 🝖 identityᵣ(_++_)(∅))
      proof {z ⊰ zl} {∅}      {y ⊰ yl} p with () ← [∅]-postpend-unequal(symmetry(_≡_) (proof{zl}{∅}{postpend z yl} ([⊰]-generalized-cancellationₗ p 🝖 symmetry(_≡_) ([++]-middle-prepend-postpend {x = z}{l₁ = yl}{l₂ = zl}))))
      proof {∅}      {x ⊰ xl} {∅}      p with () ← [∅][⊰]-unequal {l = xl} (symmetry(_≡_) p 🝖 identityᵣ(_++_)(∅))
      proof {z ⊰ zl} {x ⊰ xl} {∅}      p with () ← [∅]-postpend-unequal(proof{zl}{postpend z xl}{∅} ([++]-middle-prepend-postpend {x = z}{l₁ = xl}{l₂ = zl} 🝖 [⊰]-generalized-cancellationₗ p))

  reverse-involution-raw : Names.Involution(reverse{T = T})
  reverse-involution-raw {x = ∅}     = reflexivity(_≡_)
  reverse-involution-raw {x = x ⊰ l} = reverse-postpend {a = x}{l = reverse l} 🝖 congruence₂ᵣ(_⊰_)(x) (reverse-involution-raw {x = l})

  instance
    reverse-involution : Involution(reverse{T = T})
    Involution.proof reverse-involution = reverse-involution-raw

  initial-of-∅ : (initial(n)(∅ {T = T}) ≡ ∅)
  initial-of-∅ {n = 𝟎}    = reflexivity(_≡_)
  initial-of-∅ {n = 𝐒(n)} = reflexivity(_≡_)


  module _ where
    open import Relator.Equals.Proofs.Equiv {T = ℕ}
    foldᵣ-constant-[+]ᵣ : ∀{init step} → (foldᵣ (const(_+ step)) init l ≡ₑ (step ⋅ length(l)) + init)
    foldᵣ-constant-[+]ᵣ {l = ∅} = reflexivity(_≡ₑ_)
    foldᵣ-constant-[+]ᵣ {l = x ⊰ l} {init}{step} =
      const(_+ step) x (foldᵣ (const(_+ step)) init l) 🝖[ _≡_ ]-[]
      (foldᵣ (const(_+ step)) init l) + step           🝖[ _≡_ ]-[ congruence₁(_+ step) (foldᵣ-constant-[+]ᵣ {l = l} {init}{step}) ]
      ((step ⋅ length(l)) + init) + step               🝖[ _≡_ ]-[ One.commuteᵣ-assocₗ {a = step ⋅ length(l)}{init}{step} ]
      ((step ⋅ length(l)) + step) + init               🝖[ _≡_ ]-[ congruence₁(_+ init) (commutativity(_+_) {step ⋅ length(l)}{step}) ]
      (step + (step ⋅ length(l))) + init               🝖-end

    foldᵣ-constant-[+]ₗ : ∀{init step} → (foldᵣ (const(step +_)) init l ≡ (length(l) ⋅ step) + init)
    foldᵣ-constant-[+]ₗ {l = ∅}                  = reflexivity(_≡_)
    foldᵣ-constant-[+]ₗ {l = x ⊰ l} {init}{step} =
      foldᵣ(const(step +_)) init (x ⊰ l)  🝖[ _≡_ ]-[]
      step + foldᵣ(const(step +_)) init l 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(step) (foldᵣ-constant-[+]ₗ {l = l} {init}{step}) ]
      step + ((length(l) ⋅ step) + init)  🝖[ _≡_ ]-[ associativity(_+_) {step}{length(l) ⋅ step}{init} ]-sym
      (step + (length(l) ⋅ step)) + init  🝖[ _≡_ ]-[ congruence₂ₗ(_+_)(init) (commutativity(_+_) {step}{length(l) ⋅ step}) ]
      ((length(l) ⋅ step) + step) + init  🝖[ _≡_ ]-[ congruence₂ₗ(_+_)(init) ([⋅]-with-[𝐒]ₗ {length(l)}{step}) ]-sym
      (𝐒(length(l)) ⋅ step) + init        🝖[ _≡_ ]-[]
      (length(x ⊰ l) ⋅ step) + init       🝖-end

  instance
    [++^]-identityᵣ : Identityᵣ(_++^_ {T = T})(𝟏)
    [++^]-identityᵣ = intro p where
      p : Names.Identityᵣ(_++^_)(𝟏)
      p{∅}     = reflexivity(_≡_)
      p{x ⊰ l} = congruence₂ᵣ(_⊰_)(x) (p{l})

open import Structure.Setoid
module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-List₁ : Equiv{ℓₑₗ₁}(List(A)) ⦄ ⦃ extensionality-A : Extensionality(equiv-List₁) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ ⦃ equiv-List₂ : Equiv{ℓₑₗ₂}(List(B)) ⦄ ⦃ extensionality-B : Extensionality(equiv-List₂) ⦄
  where

  private variable l l₁ l₂ : List(T)
  private variable a b x : T
  private variable P : List(T) → Stmt{ℓ}

  private variable f g : A → B

  map-postpend : (map f(postpend a l) ≡ postpend (f(a)) (map f(l)))
  map-postpend {f = f} {a = a}{l = l} = elim (reflexivity(_≡_)) (\x l → congruence₂ᵣ(_⊰_)(f(x)) {map f (postpend a l)}{postpend (f(a)) (map f l)}) l

  instance
    map-preserves-[++] : Preserving₂(map f)(_++_)(_++_)
    Preserving.proof (map-preserves-[++] {f = f}) {l₁} {l₂} = elim (reflexivity(_≡_)) (\x l₁ → congruence₂ᵣ(_⊰_)(f(x)) {map f(l₁ ++ l₂)}{(map f l₁) ++ (map f l₂)}) l₁

  open import Function.Equals using (_⊜_)
  open import Logic.Propositional
  open import Syntax.Implication
  map-operator-raw : ∀ ⦃ func-f : Function(f) ⦄ → (f ⊜ g) → (l₁ ≡ l₂) → (map f(l₁) ≡ map g(l₂))
  map-operator-raw {f} {g} {∅}       {∅}       fg xy = reflexivity(_≡_)
  map-operator-raw {f} {g} {∅}       {x₂ ⊰ l₂} fg xy with () ← [∅][⊰]-unequal xy
  map-operator-raw {f} {g} {x₁ ⊰ l₁} {∅}       fg xy with () ← [∅][⊰]-unequal (symmetry(_≡_) xy)
  map-operator-raw {f} {g} {x₁ ⊰ l₁} {x₂ ⊰ l₂} fg xy =
    • (
      f(x₁) 🝖[ _≡_ ]-[ congruence₁(f) ([∧]-elimₗ([⊰]-generalized-cancellation xy)) ]
      f(x₂) 🝖[ _≡_ ]-[ _⊜_.proof fg {x₂} ]
      g(x₂) 🝖-end
    )
    • (
      map f(l₁) 🝖[ _≡_ ]-[ map-operator-raw fg ([∧]-elimᵣ([⊰]-generalized-cancellation xy)) ]
      map g(l₂) 🝖-end
    )
    ⇒₂-[ congruence₂(_⊰_) ]
    (f(x₁) ⊰ map f(l₁) ≡ g(x₂) ⊰ map g(l₂)) ⇒-end

  map-injective : ⦃ inj : Injective(f) ⦄ → Injective(map f)
  map-injective {f = f} = intro proof where
    proof : Names.Injective(map f)
    proof {∅}      {∅}      p = reflexivity(_≡_)
    proof {∅}      {y ⊰ yl} p with () ← [∅][⊰]-unequal p
    proof {x ⊰ xl} {∅}      p with () ← [∅][⊰]-unequal (symmetry(_≡_) p)
    proof {x ⊰ xl} {y ⊰ yl} p = congruence₂(_⊰_)
      (injective(f) ([∧]-elimₗ([⊰]-generalized-cancellation p)))
      (proof {xl} {yl} ([∧]-elimᵣ([⊰]-generalized-cancellation p)))

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-List₁ : Equiv{ℓₑₗ₁}(List(A)) ⦄ ⦃ extensionality-A : Extensionality(equiv-List₁) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  where

  private variable _▫₁_ _▫₂_ : A → B → B
  private variable id₁ id₂ : T
  private variable l l₁ l₂ : List(T)

  foldᵣ-operator-raw : ∀ ⦃ oper₁ : BinaryOperator(_▫₁_) ⦄ → (∀{x y} → (x ▫₁ y) ≡ (x ▫₂ y)) → (id₁ ≡ id₂) → (l₁ ≡ l₂) → (foldᵣ(_▫₁_) id₁ l₁ ≡ foldᵣ(_▫₂_) id₂ l₂)
  foldᵣ-operator-raw {l₁ = ∅} {l₂ = ∅} op-eq id-eq l-eq = id-eq
  foldᵣ-operator-raw {l₁ = ∅} {l₂ = x ⊰ l₂} op-eq id-eq l-eq with () ← [∅][⊰]-unequal l-eq
  foldᵣ-operator-raw {l₁ = x ⊰ l₁} {l₂ = ∅} op-eq id-eq l-eq with () ← [∅][⊰]-unequal (symmetry(_≡_) l-eq)
  foldᵣ-operator-raw {_▫₁_ = _▫₁_} {_▫₂_ = _▫₂_} {id₁}{id₂} {x₁ ⊰ l₁} {x₂ ⊰ l₂} op-eq id-eq l-eq =
    foldᵣ(_▫₁_) id₁ (x₁ ⊰ l₁) 🝖[ _≡_ ]-[]
    x₁ ▫₁ foldᵣ(_▫₁_) id₁ l₁ 🝖[ _≡_ ]-[ congruence₂(_▫₁_) ([⊰]-generalized-cancellationᵣ l-eq) (foldᵣ-operator-raw {l₁ = l₁}{l₂ = l₂} op-eq id-eq ([⊰]-generalized-cancellationₗ l-eq)) ]
    x₂ ▫₁ foldᵣ(_▫₂_) id₂ l₂ 🝖[ _≡_ ]-[ op-eq ]
    x₂ ▫₂ foldᵣ(_▫₂_) id₂ l₂ 🝖[ _≡_ ]-[]
    foldᵣ(_▫₂_) id₂ (x₂ ⊰ l₂) 🝖-end

module _ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄ where
  private variable _▫_ : B → C → C
  private variable f : A → B
  private variable id : C

  foldᵣ-map-preserve : ⦃ oper : BinaryOperator(_▫_) ⦄ → ∀{l} → (foldᵣ((_▫_) ∘ f) id l ≡ foldᵣ(_▫_) id (map f(l)))
  foldᵣ-map-preserve                  {l = ∅}     = reflexivity(_≡_)
  foldᵣ-map-preserve{_▫_ = _▫_}{f = f}{l = x ⊰ l} = congruence₂ᵣ(_▫_)(f(x)) (foldᵣ-map-preserve{_▫_ = _▫_}{f = f}{l = l})

module _ ⦃ equiv-B : Equiv{ℓₑ}(Option(B)) ⦄ where
  private variable f : A → B
  private variable l : List(A)

  first-preserve-map : first(map f(l)) ≡ Option.map f(first l)
  first-preserve-map {l = ∅}     = reflexivity(_≡_)
  first-preserve-map {l = _ ⊰ _} = reflexivity(_≡_)
