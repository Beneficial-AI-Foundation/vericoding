/-
Chef Tobby asked Bhuvan to brush up his knowledge of statistics for a test. While studying some distributions, Bhuvan learns the fact that for symmetric distributions, the mean and the median are always the same.
Chef Tobby asks Bhuvan out for a game and tells him that it will utilize his new found knowledge. He lays out a total of 109 small tiles in front of Bhuvan. Each tile has a distinct number written on it from 1 to 109.
Chef Tobby gives Bhuvan an integer N and asks him to choose N distinct tiles and arrange them in a line such that the mean of median of all subarrays lies between [N-1, N+1], both inclusive. The median of subarray of even length is the mean of the two numbers in the middle after the subarray is sorted
Bhuvan realizes that his book didn’t teach him how to solve this and asks for your help. Can you solve the problem for him?
In case, no solution exists, print -1.

-----Input section-----
First line contains, T, denoting the number of test cases.
Each of the next T lines, contain a single integer N.

-----Output section-----
If no solution, exists print -1.
If the solution exists, output N space separated integers denoting the elements of the array A such that above conditions are satisfied. In case, multiple answers exist, you can output any one them.

-----Input constraints-----
1 ≤ T ≤ 20
1 ≤ N ≤ 100

-----Sample Input-----
3
1
2
3

-----Sample Output-----
1
1 2
1 2 3

-----Explanation-----
For test case 3, the subarrays and their median are as follows: 
- {1}, median = 1
- {2}, median = 2
- {3}, median = 3
- {1, 2}, median = 1.5
- {2, 3}, median = 2.5
- {1, 2, 3}, median = 2
The mean of the medians is 2 which lies in the range [2, 4]
-/

-- <vc-helpers>
-- </vc-helpers>

def arrange_tiles (n : Int) : String := sorry

theorem invalid_inputs {n : Int}
  (h : n ≤ 0) : arrange_tiles n = "-1" := sorry

theorem valid_inputs_first_element {n : Int}
  (h : n > 0) : 
  let numbers := (arrange_tiles n).split (· = ' ')
  numbers.get? 0 = some (toString n) := sorry

theorem valid_inputs_length {n : Int}
  (h : n > 0) :
  let numbers := (arrange_tiles n).split (· = ' ')
  numbers.length = n := sorry

theorem valid_inputs_alternating {n : Int} (h : n > 1)
  (i : Nat) (h2 : i < n - 1) :
  let numbers := (arrange_tiles n).split (· = ' ') |>.map String.toInt!
  numbers[i+1]? = some (n + (i+2)/2) ∧ 
  numbers[i+2]? = some (n - (i+2)/2) := sorry

theorem unique_elements {n : Int}
  (h : n > 0) :
  let numbers := (arrange_tiles n).split (· = ' ') |>.map String.toInt!
  numbers.eraseDups = numbers := sorry

/-
info: '1'
-/
-- #guard_msgs in
-- #eval arrange_tiles 1

/-
info: '2 3'
-/
-- #guard_msgs in
-- #eval arrange_tiles 2

/-
info: '3 4 2'
-/
-- #guard_msgs in
-- #eval arrange_tiles 3

-- Apps difficulty: interview
-- Assurance level: unguarded