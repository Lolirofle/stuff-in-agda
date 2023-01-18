module Type.W where

import      Lvl
open import Functional using (id)
open import DependentFunctional using (_∘_)
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable A : Type{ℓ}
private variable B : A → Type{ℓ}

-- Types with terms that are well-founded trees.
-- Constructs types that are similar to some kind of tree.
-- The first parameter is the index for a constructor.
-- The second parameter is the arity for each constructor.
--
-- A type able to describe all non-dependent inductively defined data types assuming there are some previously defined types.
-- When described like this, the parameters should be interpreted as the following:
-- • The first parameter `A` indicates the "number" of branches based on another type's "cardinality" and should also contain the data for every branch.
-- • The second parameter `B` is used when the type to be defined refers to itself.
-- Examples:
--   open import Data
--   open import Data.Boolean
--
--   module _ (L R : Type{Lvl.𝟎}) where
--     E : Type{Lvl.𝟎}
--     E = W{A = Σ(Bool)(if_then R else L)}(const Empty) -- Either type using W.
--     l : L → E                                         -- Left branch introduction.
--     l x = sup (intro 𝐹 x) empty
--     r : R → E                                         -- Rght branch introduction.
--     r x = sup (intro 𝑇 x) empty
--
--   N = W{A = Bool}(if_then Unit{Lvl.𝟎} else Empty{Lvl.𝟎}) -- Natural numbers using W.
--   z : N                                                  -- Zero branch introduction.
--   z = sup 𝐹 empty
--   z' : _ → N                                             -- Zero branch introduction (defined like this because empty functions are not unique (from no function extensionality) resulting in more than one zero for this definition of the natural numbers).
--   z' empty = sup 𝐹 empty
--   s : N → N                                              -- Successor branch introduction.
--   s n = sup 𝑇 (\{<> → n})
--   e : ∀{P : N → Type{Lvl.𝟎}} → (∀{empty} → P(z empty)) → (∀{n} → P(n) → P(s n)) → (∀{n} → P(n)) -- TODO: Is this a correct eliminator? Note: It does not pass the termination checker
--   e pz ps {sup 𝐹 b} = pz
--   e pz ps {sup 𝑇 b} = ps (e pz (\{n} → ps{n}) {b <>})
--
-- Defined using a record:
--   record W {A : Type{ℓ₁}} (B : A → Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
--     inductive
--     eta-equality
--     constructor sup
--     field
--       a : A
--       b : B(a) → W(B)
data W (A : Type{ℓ₁}) (B : A → Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  sup : (a : A) → (b : B(a) → W A B) → W A B

label : W A B → A
label(sup a _) = a

recursor : (w : W A B) → B(label w) → W A B
recursor(sup _ b) = b

module _
  (P : W A B → Type{ℓ})
  (p : ∀{a : A}{b : B(a) → W A B} → ((ba : B(a)) → P(b(ba))) → P(sup a b))
  where

  elim : (w : W A B) → P(w)
  elim(sup a b) = p(elim ∘ b)

-- Note: This is essentially Sets.IterativeSet.
V : ∀{ℓ₁} → Type{Lvl.𝐒(ℓ₁)}
V{ℓ₁} = W(Type{ℓ₁}) id
