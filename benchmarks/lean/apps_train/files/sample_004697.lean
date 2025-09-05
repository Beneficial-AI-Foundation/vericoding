# Story

Those pesky rats have returned and this time they have taken over the Town Square.

The Pied Piper has been enlisted again to play his magical tune and coax all the rats towards him.

But some of the rats are deaf and are going the wrong way!

# Kata Task

How many deaf rats are there?

## Input Notes

* The Town Square is a rectangle of square paving stones (the Square has 1-15 pavers per side)
* The Pied Piper is always present

## Output Notes
* Deaf rats are those that are moving to paving stone **further away** from the Piper than where they are now
* Use Euclidian distance for your calculations

## Legend

* `P` = The Pied Piper
* `←` `↑` `→` `↓` `↖` `↗` `↘` `↙` = Rats going in different directions
* space = Everything else

# Examples

ex1 - has 1 deaf rat

↗ P              
  ↘   ↖
  ↑              
↗        

---

ex2 - has 7 deaf rats

    ↗            
P ↓   ↖ ↑
    ←   ↓
  ↖ ↙   ↙
↓ ↓ ↓

def DIRS := [('←', (0,-1)), ('↑', (-1,0)), ('→', (0,1)), ('↓', (1,0)),
            ('↖', (-1,-1)), ('↗', (-1,1)), ('↘', (1,1)), ('↙', (1,-1))]

def count_deaf_rats (town: List String) : Nat :=
  sorry

def listSum : List Nat → Nat 
  | [] => 0
  | x::xs => x + listSum xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
