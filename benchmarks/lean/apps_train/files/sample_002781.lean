You have stumbled across the divine pleasure that is owning a dog and a garden. Now time to pick up all the cr@p! :D

Given a 2D array to represent your garden, you must find and collect all of the dog cr@p - represented by '@'.

You will also be given the number of bags you have access to (bags), and the capactity of a bag (cap). If there are no bags then you can't pick anything up, so you can ignore cap.

You need to find out if you have enough capacity to collect all the cr@p and make your garden clean again. 

If you do, return 'Clean', else return 'Cr@p'.

Watch out though - if your dog is out there ('D'), he gets very touchy about being watched. If he is there you need to return 'Dog!!'.

For example:

x=
[[\_,\_,\_,\_,\_,\_]
 [\_,\_,\_,\_,@,\_]
 [@,\_,\_,\_,\_,\_]]

bags = 2, cap = 2

return  --> 'Clean'

def crap (garden : List (List Cell)) (bags : Nat) (cap : Nat) : GardenResult :=
  sorry

def countCrap (garden : List (List Cell)) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded