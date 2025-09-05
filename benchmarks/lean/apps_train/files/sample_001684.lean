You are in the capital of Far, Far Away Land, and you have heard about this museum where the royal family's crown jewels are on display. Before you visit the museum, a friend tells you to bring some extra money that you'll need to bribe the guards. You see, he says, the crown jewels are in one of 10 rooms numbered from 1 to 10. The doors to these room are kept closed, and each is guarded by a very intimidating guard.

For security purposes, the jewels are moved every night to a different room. To find out which room they are in, you'll have to ask one of the guards. But first you have to pay him a bribe. After paying him:

  1. If the jewels are behind the door he's guarding, he'll let you in.
  2. Otherwise, he'll point you in the direction of the correct room by telling you if the room has a higher or lower room number than the room he's guarding.

The guards have a special rank system, and, depending on rank, the size of the bribe that you'll need to pay to each guard may vary. For example, you may have to pay $1 to the guard at room 1, $2 to the guard at room 2, and so on, up to $10 to the guard at room 10. The bribe amounts are specified by an array/list sorted by room number in ascending order. Hence, in this example, the bribes are given by `[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]`.

The problem you need to solve is to determine the minimum amount you may need _in the worst case_ to get into the room with the crown jewels. As a seasoned programmer, you might try doing a binary search. Let's assume that the bribes are as specified in the example above. You first go to the guard standing in front of room 5, and pay him $5. In the worst case the crown jewels are in room 10 and you'll end up paying: $5 + $8 + $9 + $10 = $32. It turns out that a regular binary search is not optimal in this case. You are better off if you first go to room 7. In the worst case the guard will direct you to the right(i.e., higher numbered rooms) and then you go to room 9. Again, in the worst case the guard will direct you to the right, and you go to room 10. In all, you'll have to pay $7 + $9 + $10 = $26. You can easily verify that if the first guard (at room 7) had directed you to the left, you would have ended up paying less than $26. So for this problem, the maximum you will need to pay is $26. There are no other solutions where you would need less in the worst case, so 26 is the solution to this problem instance. 

You are asked to define function `least_bribes(bribes)` that takes as argument an array that contains the bribes that each guard will accept in ascending room number and returns the minumum amount you'll need to spend on bribes _in the worst case_. The problem is not limited to 10 rooms only, so the array `bribes` can be of any length greater or equal to 1. Your code will have to handle arrays up to 100 in length and bribes between $1 and $1000.

def List.sum : List Nat → Nat
  | [] => 0
  | x::xs => x + sum xs

def List.minimum : (l : List Nat) → l ≠ [] → Nat
  | [], h => by contradiction
  | [x], _ => x
  | (x::y::xs), _ => Nat.min x (minimum (y::xs) (by simp))

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded