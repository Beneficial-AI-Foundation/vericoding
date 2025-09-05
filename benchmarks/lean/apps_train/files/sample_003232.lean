With one die of 6 sides we will have six different possible results:```  1, 2, 3, 4, 5, 6``` .

With 2 dice of six sides, we will have 36 different possible results:
``` 
(1,1),(1,2),(2,1),(1,3),(3,1),(1,4),(4,1),(1,5),
(5,1), (1,6),(6,1),(2,2),(2,3),(3,2),(2,4),(4,2),
(2,5),(5,2)(2,6),(6,2),(3,3),(3,4),(4,3),(3,5),(5,3),
(3,6),(6,3),(4,4),(4,5),(5,4),(4,6),(6,4),(5,5),
(5,6),(6,5),(6,6)
``` 
So, with 2 dice of 6 sides we get 36 different events.
``` 
([6,6] ---> 36)
``` 
But with 2 different dice we can get for this case, the same number of events.
One die of ```4 sides```  and another of ```9 sides```  will produce the exact amount of events.
``` 
([4,9] ---> 36)
``` 
We say that the dice set ```[4,9]``` is equivalent to ```[6,6]``` because both produce the same number of events.

Also we may have an amount of three dice producing the same amount of events. It will be for:
``` 
[4,3,3] ---> 36
``` 
(One die of 4 sides and two dice of 3 sides each)

Perhaps you may think that the following set is equivalent: ```[6,3,2]``` but unfortunately dice have a **minimum of three sides** (well, really a 
tetrahedron with one empty side)

The task for this kata is to get the amount of equivalent dice sets, having **2 dice at least**,for a given set.

For example, for the previous case: [6,6] we will have 3 equivalent sets that are: ``` [4, 3, 3], [12, 3], [9, 4]``` .

You may assume that dice are available from 3 and above for any value up to an icosahedral die (20 sides).
``` 
[5,6,4] ---> 5 (they are [10, 4, 3], [8, 5, 3], [20, 6], [15, 8], [12, 10])
``` 
For the cases we cannot get any equivalent set the result will be `0`.
For example for the set `[3,3]` we will not have equivalent dice.

Range of inputs for Random Tests:
``` 
3 <= sides <= 15
2 <= dices <= 7
``` 
See examples in the corresponding box.

Enjoy it!!

def products (n : Nat) (k m : Nat) : List (List Nat) := sorry

def eq_dice (dice : List Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
