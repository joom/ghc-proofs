{-# LANGUAGE ScopedTypeVariables, TemplateHaskell #-}
{-# OPTIONS_GHC -O -fplugin GHC.Proof.Plugin #-}
module ThTest where

import GHC.Proof.TH

makeLaws ''[]     [''Functor, ''Applicative, ''Monad]
makeLaws ''Maybe  [''Functor, ''Applicative, ''Monad]
makeLaws ''String [''Monoid]

main = putStrLn "I ran, ergo I compiled."
