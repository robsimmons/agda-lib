{-# OPTIONS --universe-polymorphism #-}

module Lib.Level where

module LEVEL where

  data Level : Set where
    Z : Level
    S : Level -> Level

  max : Level -> Level -> Level
  max  Z     m     = m
  max (S n)  Z     = S n
  max (S n) (S m)  = S (max n m)

  {-# BUILTIN LEVEL     Level #-}
  {-# BUILTIN LEVELZERO Z  #-}
  {-# BUILTIN LEVELSUC  S   #-}
  {-# BUILTIN LEVELMAX max #-}

  record Lift {a b} (A : Set a) : Set (max a b) where
    constructor lift
    field lower : A

  open Lift public
  
open LEVEL public 
  using (Z ; S ; lift ; lower ; Level) 

