{-# OPTIONS --cubical #-}

module Type.Universe where

import      Data.Either     as Lang
import      Lvl
open import Numeral.Finite  as Lang using (𝟎 ; 𝐒)
open import Numeral.Natural as Lang using (𝟎 ; 𝐒)
import Type                 as Lang
import Type.Dependent.Sigma as Lang
import Type.Identity        as Lang
import Type.W    as Lang

data Universe : Lang.Type{Lvl.𝟎}
type : Universe → Lang.Type

data Universe where
  𝕟  : Lang.ℕ → Universe
  Π  : (u : Universe) → (type u → Universe) → Universe
  Σ  : (u : Universe) → (type u → Universe) → Universe
  W  : (u : Universe) → (type u → Universe) → Universe
  -- Id : (u : Universe) → type u → type u → Universe

type(𝕟 n)      = Lang.𝕟(n)
type(Π a b)    = (A : type a) → type(b(A))
type(Σ a b)    = Lang.Σ (type a) (\A → type(b(A)))
type(W a b)    = Lang.W (type a) (\A → type(b(A)))
-- type(Id _ a b) = Lang.Id a b

open import BidirectionalFunction using (_↔_)
import      Data as Lang
open import Functional

{-
record Extensionality{ℓ} (_≡_ : ∀{x} → type(x) → type(x) → Lang.Type{ℓ}) : Lang.Type{ℓ} where
  private [_]_≡_ = \x a b → _≡_ {x} a b
  field
    𝕟-𝟎-ext : ∀{N}{n : type(𝕟(N))} → (n ≡ n)
    𝕟-𝐒-ext : ∀{N}{a b : type(𝕟(N))} → (a ≡ b) ↔ ([ 𝕟(𝐒(N)) ] 𝐒(a) ≡ 𝐒(b))
    Π-ext : ∀{A}{B}{f g : type(Π A B)} → (f ≡ g) ↔ (∀{x} → (f(x) ≡ g(x)))
    Σ-ext : ∀{A}{B}{x y : type(Σ A B)} → (x ≡ y) ↔ (Lang.Σ.left x ≡ Lang.Σ.left y) -- TODO: Should also include equivalence of right
    W-ext : ∀{A}{B}{x y : type(W A B)} → (x ≡ y) ↔ (Lang.label x ≡ Lang.label y)
-}

Bottom : Universe
Bottom = 𝕟(0)

Unit : Universe
Unit = 𝕟(1)

Bool : Universe
Bool = 𝕟(2)

_⟶_ : Universe → Universe → Universe
a ⟶ b = Π a (const b)

_⨯_ : Universe → Universe → Universe
a ⨯ b = Σ a (const b)

_‖_ : Universe → Universe → Universe
a ‖ b = W (Σ(𝕟(2)) (\{𝟎 → a ; (𝐒 𝟎) → b})) (const(𝕟(0)))

ℕ : Universe
ℕ = W Bool \{ 𝟎 → 𝕟(0) ; (𝐒 𝟎) → 𝕟(1) }

List : Universe → Universe
List t = W (Σ(𝕟(2))
  (\{ 𝟎 → 𝕟(1) ; (𝐒 𝟎) → t }))
  (\{ (Lang.intro 𝟎 _) → 𝕟(0) ; (Lang.intro (𝐒 𝟎) _) → 𝕟(1) })

BinaryTree : Universe → Universe → Universe
BinaryTree l n = W (Σ(𝕟(2))
  (\{ 𝟎 → l ; (𝐒 𝟎) → n }))
  (\{ (Lang.intro 𝟎 _) → 𝕟(0) ; (Lang.intro (𝐒 𝟎) _) → 𝕟(2) })

open import Type.Cubical.Path
open import Type.Cubical.Path.Equality
import      Type.Cubical.Path.Functions as Path

-- TODO: Move
empty-function-prop : ∀{ℓ}{T : Lang.Type{ℓ}}{f g : Lang.𝕟(𝟎) → T} → Path f g
empty-function-prop = Path.mapping \{}

-- TODO: Move
unit-function-prop : ∀{ℓ}{T : Lang.Type{ℓ}}{f g : Lang.𝕟(1) → T} → Path (f 𝟎) (g 𝟎) → Path f g
unit-function-prop fg = Path.mapping \{ {𝟎} → fg }

[‖]-introₗ : ∀{a b} → type(a) → type(a ‖ b)
[‖]-introₗ x = Lang.sup (Lang.intro 𝟎 x) \()

[‖]-introᵣ : ∀{a b} → type(b) → type(a ‖ b)
[‖]-introᵣ x = Lang.sup (Lang.intro (𝐒 𝟎) x) \()

ℕ-𝟎 : type(ℕ)
ℕ-𝟎 = Lang.sup 𝟎 \()

ℕ-𝐒 : type(ℕ) → type(ℕ)
ℕ-𝐒 n = Lang.sup (𝐒 𝟎) (const n)

List-∅ : ∀{t} → type(List t)
List-∅ = Lang.sup (Lang.intro 𝟎 𝟎) \()

List-⊰ : ∀{t} → type(t) → type(List t) → type(List t)
List-⊰ x l = Lang.sup (Lang.intro (𝐒 𝟎) x) (const l)

open import Structure.Operator
open import Structure.Relator

[‖]-elim : ∀{a b}{ℓ} → (P : type(a ‖ b) → Lang.Type{ℓ}) → (∀{x} → P([‖]-introₗ x)) → (∀{x} → P([‖]-introᵣ x)) → (∀{x} → P(x))
[‖]-elim P pl pr {Lang.sup (Lang.intro 𝟎     x) b} = substitute₁ᵣ(P) (Path.map(Lang.sup (Lang.intro 𝟎     x)) empty-function-prop) pl
[‖]-elim P pl pr {Lang.sup (Lang.intro (𝐒 𝟎) x) b} = substitute₁ᵣ(P) (Path.map(Lang.sup (Lang.intro (𝐒 𝟎) x)) empty-function-prop) pr

ℕ-elim : ∀{ℓ} → (P : type(ℕ) → Lang.Type{ℓ}) → P(ℕ-𝟎) → ((n : type(ℕ)) → P(n) → P(ℕ-𝐒 n)) → ((n : type(ℕ)) → P(n))
ℕ-elim P pz ps (Lang.sup 𝟎     b) = substitute₁ᵣ(P) (Path.map(Lang.sup 𝟎) empty-function-prop) pz
ℕ-elim P pz ps (Lang.sup (𝐒 𝟎) b) = substitute₁ᵣ(P) (Path.map(Lang.sup (𝐒 𝟎)) (unit-function-prop Path.point) ) (ps (b 𝟎) (ℕ-elim P pz ps (b 𝟎)))

List-elim : ∀{t}{ℓ} → (P : type(List t) → Lang.Type{ℓ}) → P(List-∅) → ((x : type(t)) → (l : type(List t)) → P(l) → P(List-⊰ x l)) → ((l : type(List t)) → P(l))
List-elim P pe pp (Lang.sup (Lang.intro 𝟎 𝟎)     b) = substitute₁ᵣ(P) (Path.map(Lang.sup(Lang.intro 𝟎 𝟎)) empty-function-prop) pe
List-elim P pe pp (Lang.sup (Lang.intro (𝐒 𝟎) x) b) = substitute₁ᵣ(P) (Path.map(Lang.sup(Lang.intro(𝐒 𝟎) x)) (unit-function-prop Path.point)) (pp x (b 𝟎) (List-elim P pe pp (b 𝟎)))

open import Logic.Propositional
import      Type.W.Proofs as Lang

private variable u : Universe
private variable A B : type u
private variable p : type u → Universe
private variable n : Lang.ℕ

data Data : Universe → Lang.Type{Lvl.𝟎} where
  𝕟  : Data(𝕟(n))
  Σ  : Data(Σ u p)
  W  : Data(W u p)

data Inhabited : Universe → Lang.Type{Lvl.𝟎}
data Empty : Universe → Lang.Type{Lvl.𝟎}

inhabited-correctnessᵣ : Inhabited(u) → type(u)
empty-correctnessᵣ : Empty(u) → (type(u) → ⊥)

data Inhabited where
  𝕟 : Inhabited(𝕟(𝐒(n)))
  Π : (∀{x : type(u)} → Inhabited(p(x))) → Inhabited(Π u p)
  Σ : Inhabited(u) → ∀{x : type(u)} → Inhabited(p(x)) → Inhabited(Σ u p)
  W  : (i : Inhabited(u)) → Empty(p(inhabited-correctnessᵣ i)) → Inhabited(W u p)

data Empty where
  𝕟  : Empty(𝕟(𝟎))
  Π  : (i : Inhabited(u)) → Empty(p(inhabited-correctnessᵣ i)) → Empty(Π u p)
  Σₗ : Empty(u) → Empty(Σ u p)
  Σᵣ : (∀{x : type(u)} → Empty(p(x))) → Empty(Σ u p)
  Wₗ  : Empty(u) → Empty(W u p)
  Wᵣ  : (∀{x : type(u)} → Inhabited(p(x))) → Empty(W u p)

data Finite : Universe → Lang.Type{Lvl.𝟎} where
  𝕟  : Finite(𝕟(n))
  Π  : Finite(u) → (∀{x} → Finite(p(x))) → Finite(Π u p)
  Σ  : Finite(u) → (∀{x} → Finite(p(x))) → Finite(Σ u p)
  W  : Finite(u) → (∀{x} → Empty(p(x))) → Finite(W u p)

data Countable : Universe → Lang.Type{Lvl.𝟎} where
  Π  : Finite(u) → (∀{x} → Countable(p(x))) → Countable(Π u p)
  Σₗ : Countable(u) → (∀{x} → Finite(p(x)) ∨ Countable(p(x))) → Countable(Σ u p)
  Σᵣ : Finite(u) → (∀{x} → Finite(p(x)) ∨ Countable(p(x))) → ∀{x} → Countable(p(x)) → Countable(Σ u p)
  W  : Countable(u) → (∀{x} → Finite(p(x))) → Countable(W u p)

inhabited-correctnessᵣ 𝕟 = 𝟎
inhabited-correctnessᵣ (Π i) = \_ → inhabited-correctnessᵣ i
inhabited-correctnessᵣ (Σ i j) = Lang.intro _ (inhabited-correctnessᵣ j)
inhabited-correctnessᵣ (W i j) = Lang.W-inhabitedᵣ (Lang.intro (inhabited-correctnessᵣ i) (empty-correctnessᵣ j))

empty-correctnessᵣ (Π i e) U = empty-correctnessᵣ e (U _)
empty-correctnessᵣ (Σₗ e)  U = empty-correctnessᵣ e (Lang.Σ.left U)
empty-correctnessᵣ (Σᵣ e)  U = empty-correctnessᵣ e (Lang.Σ.right U)
empty-correctnessᵣ (Wₗ e)  U = empty-correctnessᵣ e (Lang.label U)
empty-correctnessᵣ (Wᵣ e)    = Lang.W-emptyᵣ \_ → inhabited-correctnessᵣ e

{-
finiteSize : (u : Universe) → ⦃ Finite(u) ⦄ → Lang.ℕ
finiteSize (𝕟 n)   ⦃ 𝕟 ⦄        = n
finiteSize (Π u p) ⦃ Π fin x₁ ⦄ = {!!}
finiteSize (Σ u p) ⦃ Σ fin x₁ ⦄ = {!!}
finiteSize (W u p) ⦃ W fin x₁ ⦄ = {!!}
-}

{-
inhabited-correctnessₗ : Inhabited(u) ← type(u)
empty-correctnessₗ : Empty(u) ← (type(u) → ⊥)

inhabited-correctnessₗ {𝕟 (𝐒 p)} x = 𝕟
inhabited-correctnessₗ {Π u p} x = Π \{U} → inhabited-correctnessₗ(x U)
inhabited-correctnessₗ {Σ u p} x = Σ (inhabited-correctnessₗ(Lang.Σ.left x)) (inhabited-correctnessₗ(Lang.Σ.right x))
inhabited-correctnessₗ {W u p} x = W (inhabited-correctnessₗ(Lang.label x)) (empty-correctnessₗ \PU → {!Lang.recursor x !})

empty-correctnessₗ {𝕟 𝟎}    e = 𝕟
empty-correctnessₗ {𝕟(𝐒 x)} e = [⊥]-elim (e 𝟎)
empty-correctnessₗ {Π u p}  e = Π (inhabited-correctnessₗ {!!}) {!!}
-- Π (inhabited-correctnessₗ {!!}) (empty-correctnessₗ(e ∘ {!!}))
empty-correctnessₗ {Σ u p}  e = Σᵣ (empty-correctnessₗ(\z → e (Lang.intro _ z)))
empty-correctnessₗ {W u p}  e = Wₗ (empty-correctnessₗ (e ∘ \U → inhabited-correctnessᵣ (W (inhabited-correctnessₗ U) (empty-correctnessₗ (e ∘ {!!})))))
-- Wᵣ \{U} → [⊥]-elim (e (Lang.sup U (\PU → inhabited-correctnessᵣ (W (inhabited-correctnessₗ U) {!!}))))
-- W(l(e ∘ (\U → Lang.sup U (\PU → {!PU!}))))
-}
