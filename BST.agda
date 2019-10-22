open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

module BST (X : Set)(_<_ : X → X → Set)
  (_=?_ : (x y : X) → Dec (x ≡ y))
  (_<?_ : (x y : X) → Dec (x < y))
  (_>?_ : (x y : X) → Dec (x < y)) where

data Tree : Set where
  leaf : Tree
  node : Tree → X → Tree → Tree

open import Data.List
open import Data.Bool

insert : X → Tree → Tree
insert x leaf         = node leaf x leaf
insert x (node l y r) with x <? y
insert x (node l y r) | yes p = node (insert x l) y r
insert x (node l y r) | no ¬p with y >? x
insert x (node l y r) | no ¬p | yes q = node l y (insert x r)
insert x n@(node l y r) | no ¬p | no ¬q = n

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
(x ∈T node l y r) | yes p = x ∈T l
(x ∈T node l y r) | no ¬p with x >? y
(x ∈T node l y r) | no ¬p | yes q = x ∈T r
(x ∈T node l y r) | no ¬p | no ¬q = true

_+T_ : Tree → Tree → Tree
leaf       +T ys = ys
node l x r +T ys = l +T (insert x (r +T ys))

remove : X → Tree → Tree
remove x leaf          = leaf
remove x (node l y r) with x <? y
remove x (node l y r) | yes p = node (remove x l) y r 
remove x (node l y r) | no ¬p with x >? y
remove x (node l y r) | no ¬p | yes q = node l y (remove x r)
remove x (node l y r) | no ¬p | no ¬q = l +T r

_-T_ : Tree → Tree → Tree
xs -T leaf       = xs
xs -T node l x r = remove x (xs -T l) -T r
