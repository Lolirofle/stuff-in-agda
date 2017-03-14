module String where

import Level as Lvl

postulate StringL : {n : _} → Set n
{-# BUILTIN STRING StringL #-}

String = StringL {Lvl.𝟎}
