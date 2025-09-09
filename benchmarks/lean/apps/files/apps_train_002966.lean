/-
So you've found a meeting room - phew! You arrive there ready to present, and find that someone has taken one or more of the chairs!! You need to find some quick.... check all the other meeting rooms to see if all of the chairs are in use.

Your meeting room can take up to 8 chairs. `need` will tell you how many have been taken. You need to find that many.

```if-not:java
Find the spare chairs from the array of meeting rooms. Each meeting room array will have the number of occupants as a string. Each occupant is represented by 'X'. The room array will also have an integer telling you how many chairs there are in the room.
```
```if:java
Find the spare chairs from the array of meeting rooms.
~~~java
public class Room {
  public final String occupants;  // number of occupants, each occupant is represented by 'X'
  public final int chairs;        // number of chairs in the room
}
~~~
```

You should return an array of integers that shows how many chairs you take from each room in order, up until you have the required amount.

```if-not:java
example:
[['XXX', 3], ['XXXXX', 6], ['XXXXXX', 9], ['XXX',2]] when you need 4 chairs:
```
```if:java
example:
`[Room("XXX", 3), Room("XXXXX", 6), Room("XXXXXX", 9), Room("XXX",2)]` when you need 4 chairs:
```

result -- > `[0, 1, 3]` (no chairs free in room 0, take 1 from room 1, take 3 from room 2. No need to consider room 4 as you have your 4 chairs already.

If you need no chairs, return `'Game On'`. If there aren't enough spare chairs available, return `'Not enough!'`

More in this series:

The Office I - Outed
The Office II - Boredeom Score
The Office III - Broken Photocopier
The Office IV - Find a Meeting Room
-/

def Room := (String × Nat)

def meeting (rooms : List Room) (need : Nat) : String ⊕ List Nat := sorry

def listSum : List Nat → Nat 
  | [] => 0
  | x::xs => x + listSum xs

-- <vc-helpers>
-- </vc-helpers>

def listAll : List Nat → (Nat → Bool) → Bool  
  | [], _ => true
  | x::xs, p => p x && listAll xs p

theorem meeting_zero_need {rooms : List Room} :
  meeting rooms 0 = Sum.inl "Game On" := sorry

theorem meeting_huge_need {rooms : List Room} {need : Nat} :
  (need > listSum (rooms.map (fun r => max (r.2 - r.1.length) 0))) →
  meeting rooms need = Sum.inl "Not enough!" := sorry

theorem meeting_valid_solution {rooms : List Room} {need : Nat} {result : List Nat} :
  meeting rooms need = Sum.inr result →
  (
    (result.length ≤ rooms.length) ∧
    (listAll result (fun x => x ≥ 0)) ∧
    (listSum result = need) ∧
    (rooms.zip result).all (fun p =>
      let room := p.1
      let taken := p.2
      taken ≤ max (room.2 - room.1.length) 0
    )
  ) := sorry

/-
info: [0, 1, 3]
-/
-- #guard_msgs in
-- #eval meeting [["XXX", 3], ["XXXXX", 6], ["XXXXXX", 9]] 4

/-
info: 'Game On'
-/
-- #guard_msgs in
-- #eval meeting [["XX", 2], ["XXXX", 6], ["XXXXX", 4]] 0

/-
info: [0, 2]
-/
-- #guard_msgs in
-- #eval meeting [["XX", 2], ["XXXX", 6], ["XXXXX", 4]] 2

-- Apps difficulty: introductory
-- Assurance level: unguarded