open import Type

module Graph.Walk.Functions where

open import Functional
import      Lvl
open import Graph
open import Graph.Properties
open import Graph.Walk
open import Numeral.Natural
open import Syntax.Function
open import Type.Dependent.Sigma
open import Type.Dependent.Functions

private variable ℓ : Lvl.Level
private variable T V V₁ V₂ : Type{ℓ}
private variable _⟶_ _⟶₁_ _⟶₂_ : Graph(V)
private variable a b c : V

elimFixedᵣ : ∀{b} → (P : ∀{a} → Walk(_⟶_) a b → Type{ℓ}) → (∀{x a} → (e : x ⟶ a) → (w : Walk(_⟶_) a b) → P(w) → P(prepend e w)) → P{b}(at) → (∀{a} → (w : Walk(_⟶_) a b) → P(w))
elimFixedᵣ P pp pa at            = pa
elimFixedᵣ P pp pa (prepend e w) = pp e w (elimFixedᵣ P pp pa w)

elim : (P : ∀{a b} → Walk(_⟶_) a b → Type{ℓ}) → (∀{a b c} → (e : a ⟶ b) → (w : Walk(_⟶_) b c) → P(w) → P(prepend e w)) → (∀{a} → P(at{x = a})) → (∀{a b} → (w : Walk(_⟶_) a b) → P(w))
elim P pp pa = elimFixedᵣ P pp pa

-- elimFixedₗ : ∀{a} → (P : ∀{b} → Walk(_⟶_) a b → Type{ℓ}) → (∀{b y} → (w : Walk(_⟶_) a b) → (e : b ⟶ y) → P(w) → P(postpend e w)) → P{b}(at) → (∀{b} → (w : Walk(_⟶_) a b) → P(w))

foldᵣ₁ : ∀{b} → (T : V → Type{ℓ}) → (∀{a b : V} → (a ⟶ b) → T(b) → T(a)) → T(b) → (∀{a} → Walk(_⟶_) a b → T(a))
foldᵣ₁(T) p = elimFixedᵣ(\{a} _ → T(a)) (const ∘ p)

foldᵣ₂ : (T : V → V → Type{ℓ}) → (∀{x a b : V} → (x ⟶ a) → T a b → T x b) → (∀{a : V} → T a a) → (∀{a b} → Walk(_⟶_) a b → T a b)
foldᵣ₂(T) p = elim(\{a}{b} _ → T a b) (const ∘ p)

-- Alternative implementation:
--   foldₗ₁(T) (_▫_) init at            = init
--   foldₗ₁(T) (_▫_) init (prepend x l) = foldₗ₁(T) (_▫_) (x ▫ init) l
foldₗ₁ : ∀{b} → (T : V → Type{ℓ}) → (∀{a b : V} → (a ⟶ b) → T(b) → T(a)) → T(b) → (∀{a} → Walk(_⟶_) a b → T(a))
foldₗ₁(T) (_▫_) init w = foldᵣ₁ (\x → T _ → T x) (\p rec init → p ▫ (rec init)) id w init

foldₗ₂ : (T : V → V → Type{ℓ}) → (∀{x a b : V} → (x ⟶ a) → T a b → T x b) → (∀{x} → T x x) → (∀{a b} → Walk(_⟶_) a b → T a b)
foldₗ₂(T) (_▫_) init w = foldᵣ₂(\x y → (∀{x} → T x x) → T x y) (\p rec init → p ▫ (rec init)) (\init → init) w init

-- The singleton walk consisting of only a single edge.
-- Its list counterpart is `singleton`.
edge : (a ⟶ b) → Walk(_⟶_) a b
edge e = prepend e at

-- The pair walk consisting of two edges.
-- Its list counterpart is `pair`.
join : (a ⟶ b) → (b ⟶ c) → (Walk(_⟶_) a c)
join e₁ e₂ = prepend e₁ (edge e₂)

-- Walk concatenation. Joins two paths together.
-- Its list counterpart is `_++_`.
_++_ : Walk(_⟶_) a b → Walk(_⟶_) b c → Walk(_⟶_) a c
at            ++ w₂ = w₂
prepend e₁ w₁ ++ w₂ = prepend e₁ (w₁ ++ w₂)

-- Postpending an edge to a walk, adding it to the end of the walk.
-- Its list counterpart is `postpend`.
postpend : (Walk(_⟶_) a b) → (b ⟶ c) → (Walk(_⟶_) a c)
postpend at             e₂ = edge e₂
postpend (prepend e₁ w) e₂ = prepend e₁ (postpend w e₂)

-- Reversing a walk, given that the graph is undirected.
-- Its list counterpart is `reverse`.
reverse : ⦃ Undirected(_⟶_) ⦄ → Walk(_⟶_) a b → Walk(_⟶_) b a
reverse at            = at
reverse (prepend e w) = postpend(reverse w) (undirected-reverse(_) e)

-- A walk without the edge at the start, if there is any.
-- Its list counterpart is `tail`.
-- TODO: Where did this name come from? Why did I name this "prelop" and the one below "postlop"? Maybe from a lecture?
prelop : (Walk(_⟶_) a c) → Σ(_)(b ↦ Walk(_⟶_) b c)
prelop at            = intro _ at
prelop (prepend e w) = intro _ w

-- A walk without the edge at the end, if there is any.
postlop : (Walk(_⟶_) a c) → Σ(_)(b ↦ Walk(_⟶_) a b)
postlop at                          = intro _ at
postlop (prepend e  at)             = intro _ at
postlop (prepend e₁ (prepend e₂ w)) = [Σ]-applyᵣ (postlop(prepend e₂ w)) (prepend e₁)

-- The length of the walk, the number of edges.
-- Its list counterpart is `length`.
length : (Walk(_⟶_) a b) → ℕ
length at            = 𝟎
length (prepend _ w) = 𝐒(length w)

map : (f : V₁ → V₂) → (∀{a b} → (a ⟶₁ b) → (f(a) ⟶₂ f(b))) → (Walk(_⟶₁_) a b → Walk(_⟶₂_) (f(a)) (f(b)))
map f F at = at
map f F (prepend e w) = prepend(F(e)) (map f F w)
