/-
"The Shell Game" involves cups upturned on a playing surface, with a ball placed underneath one of them.  The index of the cups are swapped around multiple times. After that the players will try to find which cup contains the ball.

Your task is as follows.  Given the cup that the ball starts under, and list of swaps, return the location of the ball at the end.  Cups are given like array/list indices.

For example, given the starting position `0` and the swaps `[(0, 1), (1, 2), (1, 0)]`:

 * The first swap moves the ball from `0` to `1`
 * The second swap moves the ball from `1` to `2`
 * The final swap doesn't affect the position of the ball.

 So

```python
find_the_ball(0, [(0, 1), (2, 1), (0, 1)]) == 2
```

There aren't necessarily only three cups in this game, but there will be at least two.  You can assume all swaps are valid, and involve two distinct indices.
-/

def find_the_ball (start : Nat) (swaps : List (Nat × Nat)) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def iterateN (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => iterateN f n (f x)

theorem find_the_ball_no_swaps (start : Nat) :
  find_the_ball start [] = start :=
sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_the_ball 5 []

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_the_ball 0 [(0, 1), (1, 2)]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_the_ball 0 [(0, 1), (1, 2), (2, 3)]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible