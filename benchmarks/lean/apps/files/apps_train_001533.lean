/-
Mance Rayder, the King-Beyond-the-Wall, has always wanted to lead the largest army the North has ever seen against the NIght’s Watch. For this humungous feat he has banded the waring tribes, the Giants, Thenns and Wildings, together by going to great extents. But the King is facing with an issue he always saw it coming.
The huge army is divided into smaller divisions and each division can be of the type $G, T$ or $W$ standing for Giants, Thenns and Wildings respectively. Mance doesn’t want two divisions of the same type standing together as he fears it might lead to a mutiny or an unorganised charge or retreat. 
For a given numbers of $G, T$ and $W$, find whether an army can be organised in accordance to the rules set by Mance. Not to forget that Mance has to include all the divisions in his battle formation in order to stand a chance against the Wall’s defences.

-----Input:-----
- First line will contain $N$, the number of test cases.
- Each of the next $N$ lines will contain three integers $G$, $T$ and $W$ - the number of Giant, Thenn and Wildling divisions respectively.

-----Output:-----
For each testcase, output in a single line $Yes$ if a battle formation is possible or $No$ otherwise.

-----Constraints-----
- $1 \leq N \leq 100$
- $1 \leq G,T,W \leq 10^9$

-----Sample Input:-----
1
1 2 1

-----Sample Output:-----
Yes

-----Explanation:-----
The first case can be formed as : $ TGWT $. Hence the answer is $ Yes $.
-/

-- <vc-helpers>
-- </vc-helpers>

def can_form_army (g t w : Nat) : String := sorry

def sorted_list (a b c : Nat) : List Nat :=
  let list := [a, b, c]
  if a ≤ b then
    if b ≤ c then [a, b, c]
    else if a ≤ c then [a, c, b]
    else [c, a, b]
  else if a ≤ c then [b, a, c]
  else if b ≤ c then [b, c, a]
  else [c, b, a]

theorem can_form_army_valid_output (g t w : Nat) :
  can_form_army g t w = "Yes" ∨ can_form_army g t w = "No" := sorry

theorem can_form_army_commutative_1 (g t w : Nat) :
  can_form_army g t w = can_form_army t g w := sorry

theorem can_form_army_commutative_2 (g t w : Nat) :
  can_form_army g t w = can_form_army w t g := sorry

theorem can_form_army_equal_positive (n : Nat) (h : n > 0) :
  can_form_army n n n = "Yes" := sorry

theorem can_form_army_sum_criterion {g t w : Nat} :
  let nums := sorted_list g t w
  (nums[0]! + nums[1]! ≥ nums[2]!) → can_form_army g t w = "Yes" := sorry

theorem can_form_army_sum_criterion_converse {g t w : Nat} :
  let nums := sorted_list g t w
  can_form_army g t w = "Yes" → (nums[0]! + nums[1]! ≥ nums[2]!) := sorry

theorem can_form_army_boundary_1 : 
  can_form_army 1 1 1 = "Yes" := sorry

theorem can_form_army_boundary_2 :
  can_form_army 100 100 100 = "Yes" := sorry

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval can_form_army 1 2 1

/-
info: 'No'
-/
-- #guard_msgs in
-- #eval can_form_army 1 1 3

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval can_form_army 2 2 2

-- Apps difficulty: interview
-- Assurance level: unguarded