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
  _<H_ : Hash → Hash → Set
  eqH : Decidable (λ (h h' : Hash) → h ≡ h')

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

_<I_ : Input → Input → Set
i <I j = id i <H id j ⊎ id i ≡ id j × index i < index j 

record Output where
  field address : Address
        value   : Value

open import BST Input _<I_

record Tx where
  field inputs  : Tree
        outputs : List Output
        forge   : Value
        fee     : Value

open Output
open Tx

llookup : Id → Ledger → Maybe Tx
llookup i []       = nothing
llookup i (t ∷ ts) with eqH i (hash t)
... | yes p = just t
... | no ¬p = llookup i ts

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

unspentOutputs : Tx → Tree
unspentOutputs tx = fromList (help 0 (outputs tx))
  where
  help : ℕ → List Output → List Input
  help n []       = []
  help n (o ∷ os) = record { id = hash tx ; index = n } ∷ help (suc n) os

-- the outputs that have been spent for a tx

spentOutputs : Tx → Tree
spentOutputs tx = inputs tx

-- computing the set of unspent outputs

utxo : Ledger → Tree
utxo []         = fromList []
utxo (tx ∷ txs) = (utxo txs -T (spentOutputs tx)) +T unspentOutputs tx

-- Definition 6.

noDouble : Tx → Bool
noDouble tx = all (_∈T unspentOutputs tx) (toList (inputs tx)) 

valuePreserved : (l : Ledger)(tx : Tx) → Dec _
valuePreserved l tx =
  forge tx + sum (mapMaybe (λ i → val i l)  (toList (inputs tx)))
  Data.Nat.≟
  sum (Data.List.map value (outputs tx)) + fee tx
