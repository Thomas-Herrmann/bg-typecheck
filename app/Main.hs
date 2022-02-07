module Main where

import Index (Index (..))
import IndexNormalization (normalize)

testix = AddI (FacI 10 (NatI 10)) (FacI 5 (AddI (AddI (NatI 4) (NatI 5)) (VarI 0)))

main :: IO ()
main = print testix >> print (normalize testix)
