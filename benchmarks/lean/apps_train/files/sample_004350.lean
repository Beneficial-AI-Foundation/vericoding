The Spelling Bee bees are back...

# How many bees are in the beehive?

* bees can be facing UP, DOWN, LEFT, RIGHT, and now also _diagonally_ up/down/left/right
* bees can share parts of other bees

## Examples

Ex1
```
bee.bee     
.e..e..
.b..eeb
```
_Answer: 5_

Ex2
```
beee..     
eeb.e.
ebee.b
```
_Answer: 7_

def Grid := List String

def GridList := List (List Char)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded