open import LFT hiding (Filter; [Filter])

module Parametricity where
  
  [Filter] = [Π] [Set] \ [A] → ([A] [→] [Bool]) [→] [List] [A] [→] [List] [A]

  [Id] = [Π] [Set] \ [A] → [A] [→] [A]

  [CBool] = [Π] [Set] \ [A] → [A] [→] [A] [→] [A]