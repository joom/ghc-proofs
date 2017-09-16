{-# LANGUAGE TemplateHaskell, ExplicitForAll, ScopedTypeVariables #-}
module GHC.Proof.TH (makeLaws) where

import Control.Monad
import Data.Char (toLower)
import Data.List (intersperse)
import Data.Maybe (fromMaybe)
import Data.Monoid
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import GHC.Proof

laws :: Name -> [(Name, DecsQ)]
laws n = let t = returnQ (ConT n) in [
    (''Functor, -- t is of kind * -> *
     [d|
       law1 :: $t a -> Proof
       law1 v = fmap id v
            === v

       law2 :: (a -> b) -> (b -> c) -> $t a -> Proof
       law2 f g v = fmap g (fmap f v)
                === fmap (g . f) v
     |])
  , (''Applicative, -- t is of kind * -> *
     [d|
       law1 :: $t a -> Proof
       law1 v = pure id <*> v
            === v

       law2 :: $t (b -> c) -> $t (a -> b) -> $t a -> Proof
       law2 u v w = pure (.) <*> u <*> v <*> w
                === u <*> (v <*> w)

       law3 :: forall a b. (a -> b) -> a -> Proof
       law3 f x = pure f <*> (pure x :: $t a)
              === pure (f x)
     |])
  , (''Monad, -- t is of kind * -> *
     [d|
       law1 :: a -> (a -> $t b) -> Proof
       law1 a k = (k a `seq` return a >>= k)
              === k a

       law2 :: $t a -> Proof
       law2 m = m >>= return
            === m

       law3 :: $t a -> (a -> $t b) -> (b -> $t c) -> Proof
       law3 m k h = m >>= (\x -> k x >>= str h)
               === (m >>= k) >>= str h

       return_pure :: forall a. a -> Proof
       return_pure x = (return x :: $t a)
                   === pure x

       ap_star :: $t (a -> b) -> $t a -> Proof
       ap_star f x = (f <*> x)
                 === (f `ap` x)
     |])
  , (''Monoid, -- t is of kind *
     [d|
       law1 :: $t -> Proof
       law1 a = a `mappend` mempty
            === mempty `mappend` a

       law2 :: $t -> $t -> $t -> Proof
       law2 a b c = a `mappend` (b `mappend` c)
                === (a `mappend` b) `mappend` c
     |])
  ]


-- | Concatenates name bases and creates a new name.
(+++) :: Name -> Name -> Name
(+++) a b = mkName (nameBase a ++ nameBase b)

getName :: Name -> Name -> Name
getName a b =
    mkName $ map toLower $ concat $ intersperse "_" [get a, get b, ""]
  where get n | n == ''[] = "list"
              | otherwise = nameBase n

renamedLaws :: Name -> [(Name, DecsQ)]
renamedLaws n = map f (laws n)
  where
    prefix :: Name -> Dec -> Dec
    prefix newN (SigD oldN t) = SigD (newN +++ oldN) t
    prefix newN (FunD oldN t) = FunD (newN +++ oldN) t
    prefix _ d = d
    f :: (Name, DecsQ) -> (Name, DecsQ)
    f (tc, ds) = (tc, map (prefix (getName n tc)) <$> ds)

singleTCLaws :: Name -> Name -> DecsQ
singleTCLaws n tc = fromMaybe
  (error $ "There are no laws defined for " ++ show tc)
  (lookup tc (renamedLaws n))

-- | '$(makeLaws \'\'Maybe [\'\'Functor, \'\'Applicative, \'\'Monad])'
-- | '$(makeLaws \'\'String [\'\'Monoid])'
makeLaws :: Name -> [Name] -> DecsQ
makeLaws n tcs = concat <$> mapM (singleTCLaws n) tcs
