# Magpies are my favourite birds

Baby ones even more so...

It is a little known fact^ that the black & white colours of baby magpies differ by **at least** one place and **at most** two places from the colours of the mother magpie.

So now you can work out if any two magpies may be related. 

*...and Quardle oodle ardle wardle doodle the magpies said*

# Kata Task

Given the colours of two magpies, determine if one is a possible **child** or **grand-child** of the other.

# Notes

* Each pair of birds being compared will have same number of colour areas
* `B` = Black
* `W` = White

# Example

Given these three magpies

Magpie 1  BWBWBW
Magpie 2  BWBWBB
Magpie 3  WWWWBB

You can see:
* Magpie 2 may be a child of Magpie 1 because there is only one difference
* Magpie 3 may be child of Magpie 2 because there are two differences
* So Magpie 3 may be a grand-child of Magpie 1
* On the other hand, Magpie 3 cannot be a child of Magpie 1 because there are three differences

---

DM :-)

^ *This fact is little known because I just made it up*

def BirdString := List Bird

def diffs : BirdString → BirdString → Nat
  | _, _ => sorry

def child : BirdString → BirdString → Bool
  | _, _ => sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded