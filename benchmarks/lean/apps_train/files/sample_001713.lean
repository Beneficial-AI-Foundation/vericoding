A famous casino is suddenly faced with a sharp decline of their revenues. They decide to offer Texas hold'em also online. Can you help them by writing an algorithm that can rank poker hands? 

Task:

Create a poker hand that has a constructor that accepts a string containing 5 cards:

```python
hand = PokerHand("KS 2H 5C JD TD")
```

The characteristics of the string of cards are:

A space is used as card seperator
Each card consists of two characters
The first character is the value of the card, valid characters are:
`2, 3, 4, 5, 6, 7, 8, 9, T(en), J(ack), Q(ueen), K(ing), A(ce)`
The second character represents the suit, valid characters are: 
`S(pades), H(earts), D(iamonds), C(lubs)`

The poker hands must be sortable by rank, the highest rank first:

```python
hands = []
hands.append(PokerHand("KS 2H 5C JD TD"))
hands.append(PokerHand("2C 3C AC 4C 5C"))
hands.sort() (or sorted(hands))
```

Apply the Texas Hold'em rules for ranking the cards. 
There is no ranking for the suits.
An ace can either rank high or rank low in a straight or straight flush. Example of a straight with a low ace:
`"5C 4D 3C 2S AS"`

Note:  there are around 25000 random tests, so keep an eye on performances.

def VALID_VALUES := ['2', '3', '4', '5', '6', '7', '8', '9', 'T', 'J', 'Q', 'K', 'A']
def VALID_SUITS := ['S', 'H', 'D', 'C'] 

structure Card where
  value : Char
  suit : Char
  deriving Repr

structure Hand where
  cards : List Card
  deriving Repr

def Hand.maxCount (h : Hand) : Nat := sorry
def Hand.maxCard (h : Hand) : Char := sorry 

def Hand.remaining (h : Hand) : List Char := sorry
def Hand.isFlush (h : Hand) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
