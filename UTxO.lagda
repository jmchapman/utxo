\begin{code}
open import Data.List
open import Data.Nat
open import Data.Maybe
open import Category.Monad
open import Data.Maybe.Categorical
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Bool

open import Agda.Primitive
open RawMonad {lzero} monad


postulate
  Hash : Set
  _<H_ : Hash → Hash → Bool
  _>H_ : Hash → Hash → Bool
  _eqH_ : Hash → Hash → Bool

Value : Set
Value = ℕ

-- rather than a hash we refer to the position in the ledger
Id : Set
Id = Hash

Address : Set
Address = ℕ

record Input : Set
record Output : Set
record Tx : Set
Ledger : Set

postulate hash : Tx → Hash

-- Definition 1

Ledger = List Tx

-- Definition 2

record Input where
  field id : Id
        index : ℕ

open Input

-- and ordering on inputs
open import Data.Sum
open import Data.Product

_<I?_ : ∀ i j → Bool
i <I? j with id i <H id j
(i <I? j) | true = true
(i <I? j) | false with id i eqH id j
(i <I? j) | false | true with index i <? index j
(i <I? j) | false | true | yes _ = true
(i <I? j) | false | true | no  _ = false
(i <I? j) | false | false = false

_>I?_ : ∀ i j → Bool
i >I? j with id i >H id j
(i >I? j) | true = true
(i >I? j) | false with id i eqH id j
(i >I? j) | false | true with index i >? index j
(i >I? j) | false | true | yes _ = true
(i >I? j) | false | true | no  _ = false
(i >I? j) | false | false = false

_eqI?_ : (i j : Input) → Bool
i eqI? j with id i eqH id j
(i eqI? j) | true with index i Data.Nat.≟ index j
(i eqI? j) | true | no _ = false
(i eqI? j) | true | yes _ = true
(i eqI? j) | false = false

record Output where
  field address : Address
        value   : Value

open import BST Input _eqI?_ _<I?_ _>I?_ renaming (Tree to InputSet)

record Tx where
  field inputs  : InputSet
        outputs : List Output
        forge   : Value
        fee     : Value

open Output
open Tx

llookup : Id → Ledger → Maybe Tx
llookup i []       = nothing
llookup i (t ∷ ts) with i eqH (hash t)
... | true = just t
... | false = llookup i ts

olookup : ℕ → List Output → Maybe Output
olookup _       []       = nothing
olookup zero    (o ∷ os) = just o
olookup (suc n) (o ∷ os) = olookup n os

-- Definition 3

tx : Input → Ledger → Maybe Tx
tx i l = llookup (id i) l

open import Function

-- the std-lib List lookup takes a Fin and returns X, here's a more
-- Haskell style one:

out : Input → Ledger → Maybe Output
out i l = tx i l >>= olookup (index i) ∘ outputs

val : Input → Ledger → Maybe Value
val i l = value <$> out i l

-- the new unspent outputs created by a transaction

unspentOutputs : Tx → InputSet
unspentOutputs tx = fromList (help 0 (outputs tx))
  where
  help : ℕ → List Output → List Input
  help n []       = []
  help n (o ∷ os) = record { id = hash tx ; index = n } ∷ help (suc n) os

-- the outputs that have been spent for a tx

spentOutputs : Tx → InputSet
spentOutputs tx = inputs tx

-- computing the set of unspent outputs

utxo : Ledger → InputSet
utxo []         = fromList []
utxo (tx ∷ txs) = (utxo txs -T (spentOutputs tx)) +T unspentOutputs tx

-- Definition 6.

noDouble : Tx → Bool
noDouble tx = all (_∈T unspentOutputs tx) (toList (inputs tx)) 

valuePreserved : (l : Ledger)(tx : Tx) → Bool
valuePreserved l tx with (
  forge tx + sum (mapMaybe (λ i → val i l)  (toList (inputs tx)))
  Data.Nat.≟
  sum (Data.List.map value (outputs tx)) + fee tx)
valuePreserved l tx | yes p = true
valuePreserved l tx | no ¬p = false
