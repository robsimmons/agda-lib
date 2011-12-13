{-# OPTIONS --universe-polymorphism #-}

module Lib.Level where

module LEVEL where

  postulate
    Level : Set
    LZ : Level
    LS : Level -> Level
    max : Level -> Level -> Level

  {-# BUILTIN LEVEL     Level #-}
  {-# BUILTIN LEVELZERO LZ  #-}
  {-# BUILTIN LEVELSUC  LS   #-}
  {-# BUILTIN LEVELMAX max #-}

  record Lift {a b} (A : Set a) : Set (max a b) where
    constructor lift
    field lower : A

  open Lift public
  
open LEVEL public 
  using (LZ ; LS ; lift ; lower ; Level) 

