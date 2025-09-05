# The die is cast!

Your task in this kata is to write a "dice roller" that interprets a subset of [dice notation](http://en.wikipedia.org/wiki/Dice_notation).

# Description

In most role-playing games, die rolls required by the system are given in the form `AdX`. `A` and `X` are variables, separated by the letter **d**, which stands for *die* or *dice*.

 - `A` is the number of dice to be rolled (usually omitted if 1).
 - `X` is the number of faces of each die.

Here are some examples of input:

# Modifiers

As an addition to the above rules the input may also contain modifiers in the form `+N` or `-N` where `N` is an integer.

Here are some examples of input containing modifiers:

*Modifiers must be applied **after** all dice has been summed up.*

# Output

Your function must support two types of output depending on the second argument; *verbose* and *summed*.

## Summed output
If the verbose flag isn't set your function should sum up all the dice and modifiers and return the result as an integer.

## Verbose output
With the verbose flag your function should return an object/hash containing an array (`dice`) with all the dice rolls, and a integer (`modifier`) containing the sum of the modifiers which defaults to zero.

Example of verbose output:

# Invalid input
Here are some examples of invalid inputs:

# Additional information

 - Your solution should ignore all whitespace.
 - `roll` should return `false` for invalid input.

def isInt (n : Nat) : Bool := sorry
def isDiceList (l : List Nat) : Bool := sorry

def isValidDiceDesc : String → Bool := sorry
def extractSides : String → Option Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
