module Boolean.Operators{lvl} where

open import Boolean{lvl}

-- Definition of boolean operators with conventions from logic
module Logic where
  infixl 1010 ¬_
  infixl 1005 _∧_
  infixl 1004 _∨_ _⊕_
  infixl 1003 _⇐_ _⇔_ _⇒_

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

  _⇒_ : Bool → Bool → Bool
  _⇒_ 𝑇 𝑇 = 𝑇
  _⇒_ 𝐹 𝑇 = 𝑇
  _⇒_ 𝑇 𝐹 = 𝐹
  _⇒_ 𝐹 𝐹 = 𝑇

  _⇐_ : Bool → Bool → Bool
  _⇐_ 𝑇 𝑇 = 𝑇
  _⇐_ 𝐹 𝑇 = 𝐹
  _⇐_ 𝑇 𝐹 = 𝑇
  _⇐_ 𝐹 𝐹 = 𝑇

  _⇔_ : Bool → Bool → Bool
  _⇔_ 𝑇 𝑇 = 𝑇
  _⇔_ 𝐹 𝑇 = 𝐹
  _⇔_ 𝑇 𝐹 = 𝐹
  _⇔_ 𝐹 𝐹 = 𝑇

-- Definition of boolean operators with conventions from typical programming languages
module Programming where
  open Logic

  infixl 1010 !_
  infixl 1005 _&&_
  infixl 1004 _||_

  _&&_ : Bool → Bool → Bool
  _&&_ = _∧_

  _||_ : Bool → Bool → Bool
  _||_ = _∨_

  !_ : Bool → Bool
  !_ = ¬_
