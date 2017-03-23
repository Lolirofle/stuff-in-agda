module Logic.Classic lvl where

import      Level as Lvl
open import Logic(lvl)
  renaming(Stmt to ConstructiveStmt)
open import LogicTheorems(lvl)
  using ([¬¬]-intro)

abstract
  data Wrap (X : ConstructiveStmt) : Set(Lvl.𝐒 lvl) where
    classic : X → Wrap X

  intro : {X : ConstructiveStmt} → X → Wrap X
  intro = classic

  -- TODO: Is this correct or will it lead to some weird proofs?
  -- elim : {X : ConstructiveStmt} → Wrap X → ¬ (¬ X)
  -- elim(classic x) = [¬¬]-intro(x)

  map : {X Y : ConstructiveStmt} → (X → Y) → Wrap X → Wrap Y
  map f (classic x) = classic(f x)

postulate [¬¬]-elim : {X : ConstructiveStmt} → Wrap(¬ (¬ X)) → Wrap(X)

-- excluded-middle : ∀{A : ConstructiveStmt} → Wrap(A ∨ (¬ A))
-- excluded-middle = intro(  )
