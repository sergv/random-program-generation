{-# OPTIONS_GHC -fno-warn-orphans #-}

module BignumNum (module Bignum) where

import Bignum

instance Num Bignum  where
  (+) = (.+.)
  (-) = (.-.)
  (*) = (.*.)
  fromInteger = fromNat
  signum = error "Bignum.signum not implemented"
  abs = error "Bignum.abs not implemented"
  negate = error "Bignum.negate not implemented"
