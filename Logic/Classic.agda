module Logic.Classic lvl where

open import Data
open import Functional
import      Level as Lvl
open import Logic(lvl)
  renaming(Stmt to ConstructiveStmt)
open import LogicTheorems(lvl)
  using ([¬¬]-intro ; non-contradiction)

abstract
  data Wrap (X : ConstructiveStmt) : Set(Lvl.𝐒 lvl) where
    classic : X → Wrap(X)

  intro : ∀{X : ConstructiveStmt} → X → Wrap(X)
  intro = classic

  -- TODO: Is this correct or will it lead to some weird proofs?
  -- elim : {X : ConstructiveStmt} → Wrap X → ¬ (¬ X)
  -- elim(classic x) = [¬¬]-intro(x)

  map : ∀{X Y : ConstructiveStmt} → (X → Y) → Wrap(X) → Wrap(Y)
  map f (classic x) = classic(f x)

  flatMap : ∀{X Y : ConstructiveStmt} → Wrap(X) → (X → Wrap(Y)) → Wrap(Y)
  flatMap (classic x) f = f x

postulate excluded-middle : ∀{A : ConstructiveStmt} → Wrap(A ∨ (¬ A))

[¬¬]-elim : ∀{X : ConstructiveStmt} → Wrap(¬ (¬ X)) → Wrap(X)
[¬¬]-elim {X} nnx = flatMap(excluded-middle{X})(λ xmid → flatMap(nnx)(λ nnx → intro([∨]-elim(id , nx→x(nnx) , xmid)))) where
  nx→x : (¬ (¬ X)) → (¬ X) → X
  nx→x nnx nx = [⊥]-elim(non-contradiction([∧]-intro nx nnx))
