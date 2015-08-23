{-# OPTIONS --universe-polymorphism #-}

module Lib.Level where

module LEVEL where

  open import Agda.Primitive using (Level) public
  open import Agda.Primitive using (lzero; lsuc; _⊔_)

  LZ : Level
  LZ = lzero

  LS : Level -> Level
  LS = lsuc

  max : Level -> Level -> Level
  max = _⊔_

  record Lift {a b} (A : Set a) : Set (max a b) where
    constructor lift
    field lower : A

  open Lift public
  
open LEVEL public 
  using (LZ ; LS ; lift ; lower ; Level) 

