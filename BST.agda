open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

module BST (X : Set)(_<_ : X → X → Set)
  (_=?_ : (x y : X) → Dec (x ≡ y))
  (_<?_ : (x y : X) → Dec (x < y)) where

data Tree : Set where
  leaf : Tree
  node : X → Tree → Tree → Tree

open import Data.List
open import Data.Bool

insert : X → Tree → Tree
insert x leaf         = node x leaf leaf
insert x (node y l r) with x <? y
insert x (node y l r) | yes p = node y (insert x l) r
insert x (node y l r) | no ¬p = node y l (insert x r)

toList : Tree → List X
toList leaf         = []
toList (node x l r) = toList l ++ [ x ] ++ toList r

-- from unordered list

fromList : List X → Tree
fromList [] = leaf
fromList (x ∷ xs) = insert x (fromList xs)

_∈T_ : X → Tree → Bool
x ∈T leaf       = false
x ∈T node y l r with x <? y
(x ∈T node y l r) | yes p = x ∈T l
(x ∈T node y l r) | no ¬p with x =? y
(x ∈T node y l r) | no ¬p | yes q = true
(x ∈T node y l r) | no ¬p | no ¬q = x ∈T r

_+T_ : Tree → Tree → Tree
leaf       +T ys = ys
node x l r +T ys = l +T (insert x (r +T ys))

remove : X → Tree → Tree
remove x leaf          = leaf
remove x (node y l r) with x <? y
remove x (node y l r) | yes p = node y (remove x l) r 
remove x (node y l r) | no ¬p with x =? y
remove x (node y l r) | no ¬p | yes q = l +T r
remove x (node y l r) | no ¬p | no ¬q = node y l (remove x r)

_-T_ : Tree → Tree → Tree
xs -T leaf       = xs
xs -T node x l r = remove x (xs -T l) -T r
