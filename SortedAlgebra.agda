{-# OPTIONS --sized-types #-}

module SortedAlgebra {â} where

import Function 
open import Data.Fin using (Fin)
open import Data.Nat using (â)
open import Data.Vec using (Vec; lookup)
open import Level using () renaming (suc to sucâ)
open import Relation.Binary using (REL)
open import Size

open import VecT using (zip; mapT; map)

record FunctionSignature (ð¢ : Set â) : Set â where
  constructor _â¦_
  field
      {arity} : â
      Ï*      : Vec ð¢ arity
      Ï       : ð¢

infix 4 _â¦_

record Signature : Set (sucâ â) where

  open FunctionSignature

  field
    ð¢ : Set â
    ð : Set â
    signð : ð â FunctionSignature ð¢

  open Function using (_â_)

  args = Ï* â signð
  ret  = Ï  â signð

record Î£-Algebra (Î£ : Signature) : Set (sucâ â) where

  open Signature Î£

  field
    S : ð¢ â Set â

  argType : ð â Set â
  argType f = mapT S (args f)

  retType : ð â Set â
  retType f = S (ret f)

  field
    F : â (f : ð) â argType f â retType f

record Î£-Rel {Î£} (A : Î£-Algebra Î£) (B : Î£-Algebra Î£) : Set (sucâ â) where

  open Signature Î£
  open Function using (_â_; flip)

  private
    module A = Î£-Algebra A
    module B = Î£-Algebra B

  field
    Ï      : â {Ï} â REL (A.S Ï) (B.S Ï) â
    Ï-homo :
      â (f : ð)
      â {as : A.argType f}
      â {bs : B.argType f}
      â zip Ï as bs
      â Ï (A.F f as) (B.F f bs)

  op : Î£-Rel B A
  op = record { Ï = flip Ï 
              ; Ï-homo = Î» f â Ï-homo f â VecT.op
              }

module Term (Î£ : Signature) where

  open Signature Î£

  Ctx : â â Set â
  Ctx = Vec ð¢

  data _â¢_â¨_â© {n} Î : ð¢ â Size â Set â where
    var : (i : Fin n)
        â Î â¢ lookup Î i â¨ â â©

    fun : â {s}
        â (f : ð)
        â mapT (Î â¢_â¨ s â©) (args f)
        â Î â¢ ret f â¨ â s â©

  Subst : â {n m} â Ctx n â Ctx m â Set â
  Subst Î Î = â i â Î â¢ lookup Î i â¨ â â©

  sub : â {n m} {Î : Ctx n} {Î : Ctx m}
      â Subst Î Î
      â (â {s A} â Î â¢ A â¨ s â© â Î â¢ A â¨ s â©)
  sub Ï (var x)   = Ï x
  sub Ï (fun f x) = fun f (map (sub Ï) x)

  id : â {n} {Î : Ctx n} â Subst Î Î
  id i = var i

  _â_ : â {n m o} {A : Ctx n} {B : Ctx m} {C : Ctx o}
      â Subst B C â Subst A B â Subst A C
  (f â g) i = sub f (g i)
