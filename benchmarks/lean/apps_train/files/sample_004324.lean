Flash has invited his nemesis The Turtle (He actually was a real villain! ) to play his favourite card game, SNAP. In this game a 52 card deck is dealt out so both Flash and the Turtle get 26 random cards. 

Each players cards will be represented by an array like below

Flash’s pile:
```[ 'A', '5', 'Q', 'Q', '6', '2', 'A', '9', '10', '6', '4', '3', '10', '9', '3', '8', 'K', 'J', 'J', 'K', '7', '9', '5', 'J', '7', '2' ]```

Turtle’s pile:
```[ '8', 'A', '2', 'Q', 'K', '8', 'J', '6', '4', '8', '7', 'A', '5', 'K', '3', 'Q', '6', '9', '4', '3', '4', '10', '2', '7', '10', '5' ]```

The players take it in turn to take the top card from their deck (the first element in their array) and place it in a face up pile in the middle. Flash goes first.

When a card is placed on the face up pile that matches the card it is placed on top of the first player to shout ‘SNAP!’ wins that round. Due to Flash's speed he wins every round.

Face up pile in the middle:
```[ 'A', '8', '5', 'A', 'Q', '2', 'Q', 'Q',```  =>  SNAP!

The face up pile of cards in the middle are added to the bottom of Flash's pile.

Flash’s pile after one round:
```['6', '2', 'A', '9', '10', '6', '4', '3', '10', '9', '3', '8', 'K', 'J', 'J', 'K', '7', '9', '5', 'J', '7', '2', 'A', '8', '5', 'A', 'Q', '2', 'Q', 'Q' ]```

Flash then starts the next round by putting down the next card.

When Turtle runs out of cards the game is over.

How many times does Flash get to call Snap before Turtle runs out of cards?

If both the player put down all their cards into the middle without any matches then the game ends a draw and Flash calls SNAP 0 times.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded