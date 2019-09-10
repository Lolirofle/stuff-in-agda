module Data.Boolean.Operators where

open import Data.Boolean

-- Definition of boolean operators with conventions from logic
module Logic where
  infixl 1010 ¬_
  infixl 1005 _∧_
  infixl 1004 _∨_ _⊕_
  infixl 1003 _⟵_ _⟷_ _⟶_

  _∧_ : Bool → Bool → Bool
  _∧_ 𝑇 𝑇 = 𝑇
  _∧_ 𝐹 𝑇 = 𝐹
  _∧_ 𝑇 𝐹 = 𝐹
  _∧_ 𝐹 𝐹 = 𝐹

  _∨_ : Bool → Bool → Bool
  _∨_ 𝑇 𝑇 = 𝑇
  _∨_ 𝐹 𝑇 = 𝑇
  _∨_ 𝑇 𝐹 = 𝑇
  _∨_ 𝐹 𝐹 = 𝐹

  ¬_ : Bool → Bool
  ¬_ 𝑇 = 𝐹
  ¬_ 𝐹 = 𝑇

  _⊕_ : Bool → Bool → Bool
  _⊕_ 𝑇 𝑇 = 𝐹
  _⊕_ 𝐹 𝑇 = 𝑇
  _⊕_ 𝑇 𝐹 = 𝑇
  _⊕_ 𝐹 𝐹 = 𝐹

  _⟶_ : Bool → Bool → Bool
  _⟶_ 𝑇 𝑇 = 𝑇
  _⟶_ 𝐹 𝑇 = 𝑇
  _⟶_ 𝑇 𝐹 = 𝐹
  _⟶_ 𝐹 𝐹 = 𝑇

  _⟵_ : Bool → Bool → Bool
  _⟵_ 𝑇 𝑇 = 𝑇
  _⟵_ 𝐹 𝑇 = 𝐹
  _⟵_ 𝑇 𝐹 = 𝑇
  _⟵_ 𝐹 𝐹 = 𝑇

  _⟷_ : Bool → Bool → Bool
  _⟷_ 𝑇 𝑇 = 𝑇
  _⟷_ 𝐹 𝑇 = 𝐹
  _⟷_ 𝑇 𝐹 = 𝐹
  _⟷_ 𝐹 𝐹 = 𝑇

  _⊼_ : Bool → Bool → Bool
  _⊼_ 𝑇 𝑇 = 𝐹
  _⊼_ 𝐹 𝑇 = 𝑇
  _⊼_ 𝑇 𝐹 = 𝑇
  _⊼_ 𝐹 𝐹 = 𝐹

  _⊽_ : Bool → Bool → Bool
  _⊽_ 𝑇 𝑇 = 𝐹
  _⊽_ 𝐹 𝑇 = 𝐹
  _⊽_ 𝑇 𝐹 = 𝐹
  _⊽_ 𝐹 𝐹 = 𝑇

  ⊤ : Bool
  ⊤ = 𝑇

  ⊥ : Bool
  ⊥ = 𝐹

-- Definition of boolean operators with conventions from typical programming languages
module Programming where
  open Logic using () renaming (_∧_ to _&&_ ; _∨_ to _||_ ; ¬_ to !_ ; _⟷_ to _==_ ; _⊼_ to _!=_) public
