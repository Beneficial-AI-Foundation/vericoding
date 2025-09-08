/-
After Misha's birthday he had many large numbers left, scattered across the room. Now it's time to clean up and Misha needs to put them in a basket. He ordered this task to his pet robot that agreed to complete the task at certain conditions. Before the robot puts a number x to the basket, Misha should answer the question: is it possible to choose one or multiple numbers that already are in the basket, such that their XOR sum equals x? 

If the answer is positive, you also need to give the indexes of these numbers. If there are multiple options of choosing numbers, you are allowed to choose any correct option. After Misha's answer the robot puts the number to the basket.

Initially the basket is empty. Each integer you put in the basket takes some number. The first integer you put into the basket take number 0, the second integer takes number 1 and so on.

Misha needs to clean up the place as soon as possible but unfortunately, he isn't that good at mathematics. He asks you to help him.

-----Input-----

The first line contains number m (1 ≤ m ≤ 2000), showing how many numbers are scattered around the room.

The next m lines contain the numbers in the order in which the robot puts them in the basket. Each number is a positive integer strictly less than 10^600 that doesn't contain leading zeroes. 

-----Output-----

For each number either print a 0 on the corresponding line, if the number cannot be represented as a XOR sum of numbers that are in the basket, or print integer k showing how many numbers are in the representation and the indexes of these numbers. Separate the numbers by spaces. Each number can occur in the representation at most once.

-----Examples-----
Input
7
7
6
5
4
3
2
1

Output
0
0
0
3 0 1 2
2 1 2
2 0 2
2 0 1

Input
2
5
5

Output
0
1 0

-----Note-----

The XOR sum of numbers is the result of bitwise sum of numbers modulo 2.
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_xor_basket (nums: List Nat) : List String :=
  sorry

theorem result_format {nums: List Nat} (h1: nums.length > 0) 
  (h2: ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 1000) :
  let result := solve_xor_basket nums
  (result.length = nums.length) ∧ 
  (∀ r ∈ result, 
    r = "0" ∨ 
    (let parts := r.split (· = ' ')
     let count := parts.head!.toNat!
     parts.length = count + 1 ∧
     (∀ i ∈ parts.tail, 
       let idx := i.toNat!
       0 ≤ idx ∧ idx < nums.length) ∧
     parts.tail.eraseDups = parts.tail)) :=
  sorry

theorem xor_property {nums: List Nat} (h1: nums.length > 0)
  (h2: ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 1000) :
  let result := solve_xor_basket nums
  ∀ i, i < nums.length →
    (result[i]? = some "0") ∨
    (∃ parts : List String,
     parts = (result[i]?).get!.split (· = ' ') ∧
     ∃ indices : List Nat,
     indices = parts.tail.map (·.toNat!) ∧
     (∀ idx ∈ indices, idx < nums.length) ∧
     let xor_result := indices.foldl (fun acc idx => Nat.xor acc (nums.get! idx)) 0
     xor_result = nums[i]?) :=
  sorry

-- Apps difficulty: competition
-- Assurance level: guarded