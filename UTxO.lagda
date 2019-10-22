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
  _<H?_ : Decidable _<H_
  _eqH?_ : Decidable (λ (h h' : Hash) → h ≡ h')

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

_<I?_ : ∀ i j → Dec (i <I j)
i <I? j with id i <H? id j
(i <I? j) | yes p = yes (inj₁ p)
(i <I? j) | no ¬p with id i eqH? id j
(i <I? j) | no ¬p | yes q with index i <? index j
(i <I? j) | no ¬p | yes q | yes r = yes (inj₂ (q , r))
(i <I? j) | no ¬p | yes q | no ¬r =
  no (λ { (inj₁ x) → ¬p x ; (inj₂ y) → ¬r (proj₂ y)})
(i <I? j) | no ¬p | no ¬q =
  no (λ { (inj₁ x) → ¬p x ; (inj₂ y) → ¬q (proj₁ y)})

_eqI?_ : (i j : Input) → Dec (i ≡ j)
i eqI? j with id i eqH? id j
(i eqI? j) | yes p with index i Data.Nat.≟ index j
(i eqI? j) | yes p | no ¬q = no (λ x → ¬q (cong index x))
(record { id = ._ ; index = ._ } eqI? record { id = _ ; index = _ })
  | yes refl
  | yes refl
  = yes refl 
(i eqI? j) | no ¬p = no (λ x → ¬p (cong id x))

record Output where
  field address : Address
        value   : Value

open import BST Input _<I_ _eqI?_ _<I?_ renaming (Tree to InputSet)

record Tx where
  field inputs  : InputSet
        outputs : List Output
        forge   : Value
        fee     : Value

open Output
open Tx

llookup : Id → Ledger → Maybe Tx
llookup i []       = nothing
llookup i (t ∷ ts) with i eqH? (hash t)
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

valuePreserved : (l : Ledger)(tx : Tx) → Dec _
valuePreserved l tx =
  forge tx + sum (mapMaybe (λ i → val i l)  (toList (inputs tx)))
  Data.Nat.≟
  sum (Data.List.map value (outputs tx)) + fee tx
