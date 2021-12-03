module Main where

import Prelude

import Effect (Effect)
import Free.Teletype as Teletype

main ∷ Effect Unit
main = do
  Teletype.main
