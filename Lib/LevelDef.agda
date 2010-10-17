{-# OPTIONS --universe-polymorphism #-}

module Lib.Level where

module Level where
  data Level : Set where
      Z : Level
      S : Level -> Level

  max : Level -> Level -> Level
  max  Z    m      = m
  max (S n)  Z     = S n
  max (S n) (S m)  = S (max n m)

  {-# BUILTIN LEVEL     Level #-}
  {-# BUILTIN LEVELZERO Z  #-}
  {-# BUILTIN LEVELSUC  S   #-}
  {-# BUILTIN LEVELMAX max #-}

open Level public

data ⟰ {l : Level} (A : Set l) : Set (S l) where
  up : A -> ⟰ A

⟱ : {l : Level} {A : Set l} -> ⟰ A -> A
⟱ (up x) = x

