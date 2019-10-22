open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Bool

module BST (X : Set)
  (_=?_ : (x y : X) → Bool)
  (_<?_ : (x y : X) → Bool)
  (_>?_ : (x y : X) → Bool) where

data Tree : Set where
  leaf : Tree
  node : Tree → X → Tree → Tree

open import Data.List

insert : X → Tree → Tree
insert x leaf         = node leaf x leaf
insert x (node l y r) with x <? y
insert x (node l y r) | true = node (insert x l) y r
insert x (node l y r) | false with y >? x
insert x (node l y r) | false | true = node l y (insert x r)
insert x n@(node l y r) | false | false = n

toList : Tree → List X
toList leaf         = []
toList (node l x r) = toList l ++ [ x ] ++ toList r

-- from unordered list

fromList : List X → Tree
fromList [] = leaf
fromList (x ∷ xs) = insert x (fromList xs)

_∈T_ : X → Tree → Bool
x ∈T leaf       = false
x ∈T node l y r with x <? y
(x ∈T node l y r) | true = x ∈T l
(x ∈T node l y r) | false with x >? y
(x ∈T node l y r) | false | true = x ∈T r
(x ∈T node l y r) | false | false = true

_+T_ : Tree → Tree → Tree
leaf       +T ys = ys
node l x r +T ys = l +T (insert x (r +T ys))

remove : X → Tree → Tree
remove x leaf          = leaf
remove x (node l y r) with x <? y
remove x (node l y r) | true = node (remove x l) y r 
remove x (node l y r) | false with x >? y
remove x (node l y r) | false | true = node l y (remove x r)
remove x (node l y r) | false | false = l +T r

_-T_ : Tree → Tree → Tree
xs -T leaf       = xs
xs -T node l x r = remove x (xs -T l) -T r
