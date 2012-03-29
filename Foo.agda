open import Prelude

module Foo where

ident : {A : Set} → A → A
ident x = x

foo : {A : Set} → A → A
foo = ident ident
