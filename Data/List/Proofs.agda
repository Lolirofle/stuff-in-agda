module Data.List.Proofs where

import Lvl
open import Function.EqualsRaw
open import Functional as Fn using (_∘_ ; const)
open import Data.Option using (Option ; Some ; None)
import      Data.Option.Functions as Option
open import Data.List
open import Data.List.Equiv
open import Data.List.Functions
open import Logic
open import Logic.Propositional
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

private variable ℓ ℓₑ ℓₑₗ ℓₑₒ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ ℓₑₗ₁ ℓₑₗ₂ ℓₑₗ₃ : Lvl.Level
private variable T A B C D A₁ A₂ B₁ B₂ : Type{ℓ}
private variable n : ℕ

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ equiv-List : Equiv{ℓₑₗ}(List(T)) ⦄ ⦃ extensionality : Extensionality(equiv-List) ⦄ where
  private variable l l₁ l₂ lₑ : List(T)
  private variable a b x e : T
  private variable P : List(T) → Stmt{ℓ}
  private variable _▫_ : A → B → C

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

  instance
    [++]-identityₗ : Identityₗ(_++_) ∅
    Identityₗ.proof([++]-identityₗ) = reflexivity(_≡_)

  instance
    [++]-identityᵣ : Identityᵣ(_++_) ∅
    Identityᵣ.proof([++]-identityᵣ) {x = l} = elim _ (reflexivity(_≡_)) (\x l → congruence₂-₂(_⊰_)(x) {l ++ ∅}{l}) l

  instance
    [++]-associativity : Associativity(_++_)
    Associativity.proof([++]-associativity) {l₁}{l₂}{l₃} = elim _ (reflexivity(_≡_)) (\x l → congruence₂-₂(_⊰_)(x) {(l ++ l₂) ++ l₃}{l ++ (l₂ ++ l₃)}) l₁

  instance
    [++]-function : BinaryOperator(_++_)
    [++]-function = intro p where
      p : Names.Congruence₂(_++_)
      p {∅}      {∅}      {x₂} {y₂} xy₁ xy₂ = xy₂
      p {∅}      {b ⊰ y₁} {x₂} {y₂} xy₁ xy₂ with () ← [∅][⊰]-unequal xy₁
      p {a ⊰ x₁} {∅}      {x₂} {y₂} xy₁ xy₂ with () ← [∅][⊰]-unequal (symmetry(_≡_) xy₁)
      p {a ⊰ x₁} {b ⊰ y₁} {x₂} {y₂} xy₁ xy₂ = congruence₂(_⊰_) ([⊰]-generalized-cancellationᵣ xy₁) (p{x₁}{y₁}{x₂}{y₂} ([⊰]-generalized-cancellationₗ xy₁) xy₂)

  prepend-[++] : (a ⊰ l ≡ singleton{T = T}(a) ++ l)
  prepend-[++] = reflexivity(_≡_)

  postpend-[++] : (postpend{T = T} a l ≡ l ++ singleton(a))
  postpend-[++] {a = a}{l = l} = elim _ (reflexivity(_≡_)) (\x l → congruence₂-₂(_⊰_)(x) {postpend a l}{l ++ (singleton a)}) l

  postpend-of-[++] : (postpend{T = T} a (l₁ ++ l₂) ≡ l₁ ++ postpend a l₂)
  postpend-of-[++] {a = a} {l₁}{l₂} = elim _ (reflexivity(_≡_)) (\x l → congruence₂-₂(_⊰_)(x) {postpend a (l ++ l₂)}{l ++ (postpend a l₂)}) l₁

  foldₗ-of-postpend : (foldₗ(_▫_) e (postpend x l) ≡ (foldₗ(_▫_) e l) ▫ x)
  foldₗ-of-postpend {l = ∅}     = reflexivity(_≡_)
  foldₗ-of-postpend {l = x ⊰ l} = foldₗ-of-postpend {l = l}

  [∘]-commutativity-of-postpend-prepend : postpend a ∘ prepend b ⊜ prepend b ∘ postpend a
  [∘]-commutativity-of-postpend-prepend = reflexivity(_≡_)

  foldₗ-[⊱]-move-to-end : foldₗ(_⊱_) lₑ l ≡ (foldₗ(_⊱_) ∅ l) ++ lₑ
  foldₗ-[⊱]-move-to-end {lₑ} {∅} = identityₗ(_++_)(∅)
  foldₗ-[⊱]-move-to-end {lₑ} {x ⊰ l} =
    foldₗ(_⊱_) lₑ (x ⊰ l)             🝖[ _≡_ ]-[]
    foldₗ(_⊱_) (x ⊰ lₑ) l             🝖[ _≡_ ]-[ foldₗ-[⊱]-move-to-end {x ⊰ lₑ} {l} ]
    foldₗ(_⊱_) ∅ l ++ (x ⊰ lₑ)        🝖[ _≡_ ]-[]
    foldₗ(_⊱_) ∅ l ++ ((x ⊰ ∅) ++ lₑ) 🝖[ _≡_ ]-[ associativity(_++_) {foldₗ(_⊱_) ∅ l} ]-sym
    (foldₗ(_⊱_) ∅ l ++ (x ⊰ ∅)) ++ lₑ 🝖[ _≡_ ]-[ congruence₂-₁(_++_)(lₑ) (foldₗ-[⊱]-move-to-end {x ⊰ ∅} {l}) ]-sym
    foldₗ(_⊱_) (x ⊰ ∅) l ++ lₑ        🝖[ _≡_ ]-[]
    foldₗ(_⊱_) ∅ (x ⊰ l) ++ lₑ        🝖-end

  instance
    postpend-function : BinaryOperator(postpend)
    postpend-function = intro p where
      p : Names.Congruence₂(postpend)
      p {x₂ = ∅}        {y₂ = ∅}        px pl = congruence₂(_⊰_) px pl
      p {x₂ = ∅}        {y₂ = y₂ ⊰ yl₂} px pl with () ← [∅][⊰]-unequal pl
      p {x₂ = x₂ ⊰ xl₂} {y₂ = ∅}        px pl with () ← [∅][⊰]-unequal (symmetry(_≡_) pl)
      p {x₂ = x₂ ⊰ xl₂} {y₂ = y₂ ⊰ yl₂} px pl = congruence₂(_⊰_) ([⊰]-generalized-cancellationᵣ pl) (p{x₂ = xl₂} {y₂ = yl₂} px ([⊰]-generalized-cancellationₗ pl))

  [∅]-postpend-unequal : (postpend x l ≢ ∅)
  [∅]-postpend-unequal {l = ∅}     = [∅][⊰]-unequal ∘ symmetry(_≡_)
  [∅]-postpend-unequal {l = _ ⊰ l} = [∅][⊰]-unequal ∘ symmetry(_≡_)

  postpend-unequal : (postpend x l ≢ l)
  postpend-unequal {l = ∅}     = [∅][⊰]-unequal ∘ symmetry(_≡_)
  postpend-unequal {l = y ⊰ l} = postpend-unequal {l = l} ∘ cancellationₗ(_⊰_)

  [++]-middle-prepend-postpend : postpend x l₁ ++ l₂ ≡ l₁ ++ (x ⊰ l₂)
  [++]-middle-prepend-postpend {l₁ = ∅}      {l₂ = ∅} = reflexivity(_≡_)
  [++]-middle-prepend-postpend {l₁ = ∅}      {l₂ = x ⊰ l₂} = reflexivity(_≡_)
  [++]-middle-prepend-postpend {l₁ = x ⊰ l₁} {l₂ = l₂} = congruence₂-₂(_⊰_)(x) ([++]-middle-prepend-postpend {l₁ = l₁} {l₂ = l₂})

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

  initial-of-∅ : (initial(n)(∅ {T = T}) ≡ ∅)
  initial-of-∅ {n = 𝟎}    = reflexivity(_≡_)
  initial-of-∅ {n = 𝐒(n)} = reflexivity(_≡_)


  module _ where
    open import Relator.Equals.Proofs.Equiv
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
      step + foldᵣ(const(step +_)) init l 🝖[ _≡_ ]-[ congruence₂-₂(_+_)(step) (foldᵣ-constant-[+]ₗ {l = l} {init}{step}) ]
      step + ((length(l) ⋅ step) + init)  🝖[ _≡_ ]-[ associativity(_+_) {step}{length(l) ⋅ step}{init} ]-sym
      (step + (length(l) ⋅ step)) + init  🝖[ _≡_ ]-[ congruence₂-₁(_+_)(init) (commutativity(_+_) {step}{length(l) ⋅ step}) ]
      ((length(l) ⋅ step) + step) + init  🝖[ _≡_ ]-[ congruence₂-₁(_+_)(init) ([⋅]-with-[𝐒]ₗ {length(l)}{step}) ]-sym
      (𝐒(length(l)) ⋅ step) + init        🝖[ _≡_ ]-[]
      (length(x ⊰ l) ⋅ step) + init       🝖-end

  instance
    [++^]-identityᵣ : Identityᵣ(_++^_ {T = T})(𝟏)
    [++^]-identityᵣ = intro p where
      p : Names.Identityᵣ(_++^_)(𝟏)
      p{∅}     = reflexivity(_≡_)
      p{x ⊰ l} = congruence₂-₂(_⊰_)(x) (p{l})

  foldᵣ-inverse : foldᵣ(_⊰_) ∅ ⊜ Fn.id
  foldᵣ-inverse {∅}     = reflexivity(_≡_)
  foldᵣ-inverse {x ⊰ l} = congruence₂-₂(prepend)(x) (foldᵣ-inverse {l})

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-List₁ : Equiv{ℓₑₗ₁}(List(A)) ⦄ ⦃ extensionality-A : Extensionality(equiv-List₁) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ ⦃ equiv-List₂ : Equiv{ℓₑₗ₂}(List(B)) ⦄ ⦃ extensionality-B : Extensionality(equiv-List₂) ⦄
  where

  private variable l l₁ l₂ : List(T)
  private variable a b x : T
  private variable P : List(T) → Stmt{ℓ}

  private variable f g : A → B

  map-postpend : (map f(postpend a l) ≡ postpend (f(a)) (map f(l)))
  map-postpend {f = f} {a = a}{l = l} = elim _ (reflexivity(_≡_)) (\x l → congruence₂-₂(_⊰_)(f(x)) {map f (postpend a l)}{postpend (f(a)) (map f l)}) l

  instance
    map-preserves-[++] : Preserving₂(map f)(_++_)(_++_)
    Preserving.proof (map-preserves-[++] {f = f}) {l₁} {l₂} = elim _ (reflexivity(_≡_)) (\x l₁ → congruence₂-₂(_⊰_)(f(x)) {map f(l₁ ++ l₂)}{(map f l₁) ++ (map f l₂)}) l₁

  open import Logic.Propositional
  open import Syntax.Implication

  module _ ⦃ func-fg : Function(f) ∨ Function(g) ⦄ where
    map-operator-raw : (f ⊜ g) → (l₁ ≡ l₂) → (map f(l₁) ≡ map g(l₂))
    map-operator-raw {∅}       {∅}       fg xy = reflexivity(_≡_)
    map-operator-raw {∅}       {x₂ ⊰ l₂} fg xy with () ← [∅][⊰]-unequal xy
    map-operator-raw {x₁ ⊰ l₁} {∅}       fg xy with () ← [∅][⊰]-unequal (symmetry(_≡_) xy)
    map-operator-raw {x₁ ⊰ l₁} {x₂ ⊰ l₂} fg xy =
      • ([∨]-elim
        (\func-f → let instance _ = func-f in
          f(x₁) 🝖[ _≡_ ]-[ congruence₁(f) ([∧]-elimₗ([⊰]-generalized-cancellation xy)) ]
          f(x₂) 🝖[ _≡_ ]-[ fg {x₂} ]
          g(x₂) 🝖-end
        )
        (\func-g → let instance _ = func-g in
          f(x₁) 🝖[ _≡_ ]-[ fg {x₁} ]
          g(x₁) 🝖[ _≡_ ]-[ congruence₁(g) ([∧]-elimₗ([⊰]-generalized-cancellation xy)) ]
          g(x₂) 🝖-end
        )
        func-fg
      )
      • (
        map f(l₁) 🝖[ _≡_ ]-[ map-operator-raw fg ([∧]-elimᵣ([⊰]-generalized-cancellation xy)) ]
        map g(l₂) 🝖-end
      )
      ⇒₂-[ congruence₂(_⊰_) ]
      (f(x₁) ⊰ map f(l₁) ≡ g(x₂) ⊰ map g(l₂)) ⇒-end

    map-functional-raw : (f ⊜ g) → (map f ⊜ map g)
    map-functional-raw fg = map-operator-raw fg (reflexivity(_≡_))

  instance
    map-function : ⦃ func-f : Function(f) ⦄ → Function(map f)
    map-function {f = f} ⦃ func-f ⦄ = intro (map-operator-raw ⦃ [∨]-introₗ func-f ⦄ (reflexivity(_⊜_) {f}))

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

  foldᵣ-operator-raw : ∀ ⦃ oper₁ : BinaryOperator(_▫₁_) ⦄ → ((_▫₁_) ⊜ (_▫₂_)) → (id₁ ≡ id₂) → (l₁ ≡ l₂) → (foldᵣ(_▫₁_) id₁ l₁ ≡ foldᵣ(_▫₂_) id₂ l₂)
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

  foldᵣ-map-preserve : ⦃ oper : BinaryOperator(_▫_) ⦄ → (foldᵣ((_▫_) ∘ f) id ⊜ foldᵣ(_▫_) id ∘ map f)
  foldᵣ-map-preserve                  {x = ∅}     = reflexivity(_≡_)
  foldᵣ-map-preserve{_▫_ = _▫_}{f = f}{x = x ⊰ l} = congruence₂-₂(_▫_)(f(x)) (foldᵣ-map-preserve{_▫_ = _▫_}{f = f}{x = l})

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄  where
  private variable _▫_ : T → T → T
  private variable f : T → T
  private variable id : T

  -- Note: When f is (_▫ y) for an arbitrary y, preserv of type (∀{x y} → Preserving₁ (_▫ y) (x ▫_)(x ▫_)) is associativity.
  -- Examples:
  --   𝐒(foldᵣ(_+_) 𝟎 l) = foldᵣ(_+_) 𝟏 l
  --   (foldᵣ(_+_) 5 l) + 10 = foldᵣ(_+_) 15 l
  --   f(foldᵣ(_▫_) id [a,b,c,d]) = f(a ▫ (b ▫ (c ▫ d))) = a ▫ f(b ▫ (c ▫ d)) = a ▫ (b ▫ f(c ▫ d)) =  = a ▫ (b ▫ (c ▫ f(d))) = foldᵣ(_▫_) (f(id)) [a,b,c,d]
  foldᵣ-outer-composition : ⦃ oper : BinaryOperator(_▫_) ⦄ ⦃ preserv : ∀{x} → Preserving₁ f (x ▫_)(x ▫_) ⦄ → ∀{l} → (f(foldᵣ(_▫_) id l) ≡ foldᵣ(_▫_) (f(id)) l)
  foldᵣ-outer-composition                            {l = ∅}     = reflexivity(_≡_)
  foldᵣ-outer-composition {_▫_ = _▫_}{f = f}{id = id}{l = x ⊰ l} =
    f(foldᵣ(_▫_) id (x ⊰ l))   🝖[ _≡_ ]-[]
    f(x ▫ foldᵣ(_▫_) id l)     🝖[ _≡_ ]-[ preserving₁ f (x ▫_)(x ▫_) ]
    x ▫ f(foldᵣ(_▫_) id l)     🝖[ _≡_ ]-[ congruence₂-₂(_▫_)(x) (foldᵣ-outer-composition{l = l}) ]
    x ▫ (foldᵣ(_▫_) (f(id)) l) 🝖[ _≡_ ]-[]
    foldᵣ(_▫_) (f(id)) (x ⊰ l) 🝖-end

module _ ⦃ equiv-B : Equiv{ℓₑ}(Option(B)) ⦄ where
  private variable f : A → B
  private variable l : List(A)

  first-preserve-map : first(map f(l)) ≡ Option.map f(first l)
  first-preserve-map {l = ∅}     = reflexivity(_≡_)
  first-preserve-map {l = _ ⊰ _} = reflexivity(_≡_)

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄
  ⦃ equiv-List-A : Equiv{ℓₑₗ₁}(List(A)) ⦄
  ⦃ equiv-List-B : Equiv{ℓₑₗ₂}(List(B)) ⦄
  ⦃ equiv-List-C : Equiv{ℓₑₗ₃}(List(C)) ⦄
  ⦃ ext-A : Extensionality(equiv-List-A) ⦄
  ⦃ ext-B : Extensionality(equiv-List-B) ⦄
  ⦃ ext-C : Extensionality(equiv-List-C) ⦄
  where

  private variable f : List A → List C
  private variable g : List B → List C
  private variable _▫_ : A → B → C

  instance
    map₂-function : ⦃ func-f : Function(f) ⦄ ⦃ func-g : Function(g) ⦄ ⦃ oper : BinaryOperator(_▫_) ⦄ → BinaryOperator(map₂(_▫_) f g)
    map₂-function{f = f}{g = g}{_▫_ = _▫_} = intro(\{x} → p{x}) where
      p : Names.Congruence₂(map₂(_▫_) f g)
      p{∅}     {∅}         {∅}       {∅}        xy₁ xy₂ = reflexivity(_≡_)
      p{∅}     {∅}         {∅}       {y₂ ⊰ yl₂} xy₁ xy₂ with () ← [∅][⊰]-unequal xy₂
      p{∅}     {∅}         {x₂ ⊰ xl₂}{∅}        xy₁ xy₂ with () ← [∅][⊰]-unequal(symmetry(_≡_) xy₂)
      p{∅}     {∅}         {x₂ ⊰ xl₂}{y₂ ⊰ yl₂} xy₁ xy₂ = congruence₁(g) xy₂
      p{∅}     {y₁ ⊰ yl₁}  {∅}       {∅}        xy₁ xy₂ with () ← [∅][⊰]-unequal xy₁
      p{∅}     {y₁ ⊰ yl₁}  {∅}       {y₂ ⊰ yl₂} xy₁ xy₂ with () ← [∅][⊰]-unequal xy₁
      p{∅}     {y₁ ⊰ yl₁}  {x₂ ⊰ xl₂}{∅}        xy₁ xy₂ with () ← [∅][⊰]-unequal xy₁
      p{∅}     {y₁ ⊰ yl₁}  {x₂ ⊰ xl₂}{y₂ ⊰ yl₂} xy₁ xy₂ with () ← [∅][⊰]-unequal xy₁
      p{x₁ ⊰ xl₁}{∅}       {∅}       {∅}        xy₁ xy₂ with () ← [∅][⊰]-unequal(symmetry(_≡_) xy₁)
      p{x₁ ⊰ xl₁}{∅}       {∅}       {y₂ ⊰ yl₂} xy₁ xy₂ with () ← [∅][⊰]-unequal xy₂
      p{x₁ ⊰ xl₁}{∅}       {x₂ ⊰ xl₂}{∅}        xy₁ xy₂ with () ← [∅][⊰]-unequal(symmetry(_≡_) xy₁)
      p{x₁ ⊰ xl₁}{∅}       {x₂ ⊰ xl₂}{y₂ ⊰ yl₂} xy₁ xy₂ with () ← [∅][⊰]-unequal(symmetry(_≡_) xy₁)
      p{x₁ ⊰ xl₁}{y₁ ⊰ yl₁}{∅}       {∅}        xy₁ xy₂ = congruence₁(f) xy₁
      p{x₁ ⊰ xl₁}{y₁ ⊰ yl₁}{∅}       {y₂ ⊰ yl₂} xy₁ xy₂ with () ← [∅][⊰]-unequal xy₂
      p{x₁ ⊰ xl₁}{y₁ ⊰ yl₁}{x₂ ⊰ xl₂}{∅}        xy₁ xy₂ with () ← [∅][⊰]-unequal(symmetry(_≡_) xy₂)
      p{x₁ ⊰ xl₁}{y₁ ⊰ yl₁}{x₂ ⊰ xl₂}{y₂ ⊰ yl₂} xy₁ xy₂ = congruence₂(_⊰_)
        (congruence₂(_▫_)
          ([⊰]-generalized-cancellationᵣ xy₁)
          ([⊰]-generalized-cancellationᵣ xy₂)
        )
        (p{xl₁}{yl₁}{xl₂}{yl₂}
          ([⊰]-generalized-cancellationₗ xy₁)
          ([⊰]-generalized-cancellationₗ xy₂)
        )

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-List-A : Equiv{ℓₑₗ₁}(List(A)) ⦄
  ⦃ equiv-List-B : Equiv{ℓₑₗ₂}(List(B)) ⦄
  ⦃ ext-A : Extensionality(equiv-List-A) ⦄
  ⦃ ext-B : Extensionality(equiv-List-B) ⦄
  {f g : A → List B}
  ⦃ func-fg : Function(f) ∨ Function(g) ⦄
  where

  private variable l₁ l₂ : List A

  concatMap-operator : (f ⊜ g) → (l₁ ≡ l₂) → (concatMap f l₁ ≡ concatMap g l₂)
  concatMap-operator {l₁ = ∅}      {l₂ = ∅}      pf pl = reflexivity(_≡_)
  concatMap-operator {l₁ = ∅}      {l₂ = y ⊰ l₂} pf pl with () ← [∅][⊰]-unequal pl
  concatMap-operator {l₁ = x ⊰ l₁} {l₂ = ∅}      pf pl with () ← [∅][⊰]-unequal(symmetry(_≡_) pl)
  concatMap-operator {l₁ = x ⊰ l₁} {l₂ = y ⊰ l₂} pf pl = congruence₂(_++_)
    ([∨]-elim
      (\func-f → congruence₁(f) ⦃ func-f ⦄ ([⊰]-generalized-cancellationᵣ pl) 🝖 pf)
      (\func-g → pf 🝖 congruence₁(g) ⦃ func-g ⦄ ([⊰]-generalized-cancellationᵣ pl))
      func-fg
    )
    (concatMap-operator {l₁ = l₁} {l₂ = l₂} pf ([⊰]-generalized-cancellationₗ pl))
