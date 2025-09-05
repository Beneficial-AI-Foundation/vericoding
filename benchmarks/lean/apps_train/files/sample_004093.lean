Lеt's create function to play cards. Our rules:

We have the preloaded `deck`:

```
deck = ['joker','2♣','3♣','4♣','5♣','6♣','7♣','8♣','9♣','10♣','J♣','Q♣','K♣','A♣',
                '2♦','3♦','4♦','5♦','6♦','7♦','8♦','9♦','10♦','J♦','Q♦','K♦','A♦',
                '2♥','3♥','4♥','5♥','6♥','7♥','8♥','9♥','10♥','J♥','Q♥','K♥','A♥',
                '2♠','3♠','4♠','5♠','6♠','7♠','8♠','9♠','10♠','J♠','Q♠','K♠','A♠']
```

We have 3 arguments:

`card1` and `card2` - any card of our deck.

`trump` - the main suit of four ('♣', '♦', '♥', '♠').

If both cards have the same suit, the big one wins.

If the cards have different suits (and no one has trump) return 'Let's play again.'

If one card has `trump` unlike another, wins the first one.

If both cards have `trump`, the big one wins.

If `card1` wins, return 'The first card won.' and vice versa.

If the cards are equal, return 'Someone cheats.'

A few games:

```
('3♣', 'Q♣', '♦') -> 'The second card won.'

('5♥', 'A♣', '♦') -> 'Let us play again.'

('8♠', '8♠', '♣') -> 'Someone cheats.'

('2♦', 'A♠', '♦') -> 'The first card won.'

('joker', 'joker', '♦') -> 'Someone cheats.'

```
P.S. As a card you can also get the string 'joker' - it means this card always wins.

def card_game : Card → Card → String → String := sorry

theorem identical_cards_cheating
  (card1 card2 : Card) (trump : String) :
  card1 = card2 → card_game card1 card2 trump = "Someone cheats." := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
