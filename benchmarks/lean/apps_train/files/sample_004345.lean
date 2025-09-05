# Background

My TV remote control has arrow buttons and an `OK` button.

I can use these to move a "cursor" on a logical screen keyboard to type "words"...

The screen "keyboard" layout looks like this

  #tvkb {
    width : 300px;
    border: 5px solid gray; border-collapse: collapse;
  }
  #tvkb td {
    color : orange;
    background-color : black;
    text-align : right;
    border: 3px solid gray; border-collapse: collapse;
  }

abcde123
fghij456
klmno789
pqrst.@0
uvwxyz_/

# Kata task

How many button presses on my remote are required to type a given `word`?

## Notes

* The cursor always starts on the letter `a` (top left)
* Remember to also press `OK` to "accept" each character.
* Take a direct route from one character to the next
* The cursor does not wrap (e.g. you cannot leave one edge and reappear on the opposite edge)
* A "word" (for the purpose of this Kata) is any sequence of characters available on my virtual "keyboard" 

# Example

word = `codewars`

* c => `a`-`b`-`c`-OK = 3
* o => `c`-`d`-`e`-`j`-`o`-OK = 5
* d => `o`-`j`-`e`-`d`-OK = 4
* e => `d`-`e`-OK = 2
* w => `e`-`j`-`o`-`t`-`y`-`x`-`w`-OK = 7
* a => `w`-`r`-`m`-`h`-`c`-`b`-`a`-OK = 7
* r => `a`-`f`-`k`-`p`-`q`-`r`-OK = 6
* s => `r`-`s`-OK = 2

Answer = 3 + 5 + 4 + 2 + 7 + 7 + 6 + 2 = 36

*Good Luck!
DM.*

Series
* TV Remote
* TV Remote (shift and space)
* TV Remote (wrap)
* TV Remote (symbols)

def KEYBOARD := "abcde123fghij456klmno789pqrst.@0uvwxyz_/"

def manhattan (p1 p2 : Nat × Nat) : Nat := 
  let (x1, y1) := p1
  let (x2, y2) := p2
  Nat.sub (if x2 ≥ x1 then x2 else x1) (if x2 ≥ x1 then x1 else x2) + 
  Nat.sub (if y2 ≥ y1 then y2 else y1) (if y2 ≥ y1 then y1 else y2)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded