/-
Chef likes to play with big numbers. Today, he has a big positive integer N. He can select any two digits from this number (the digits can be same but their positions should be different) and orders them in any one of the two possible ways. For each of these ways, he creates a two digit number from it (might contain leading zeros). Then, he will pick a character corresponding to the ASCII value equal to this number, i.e. the number 65 corresponds to 'A', 66 to 'B' and so on till 90 for 'Z'. Chef is only interested in finding which of the characters in the range 'A' to 'Z' can possibly be picked this way. 

-----Input-----
The first line of the input contains an integer T denoting the number of test cases.
The first line of the input contains an integer N. 

-----Output-----
For each test case, output a string containing characters Chef can pick in sorted order If the resulting size of string is zero, you should output a new line.

-----Constraints-----
- 1 ≤ T ≤ 10
- 1 ≤ N ≤ 10100000

-----Subtasks-----
- Subtask #1 (40 points) N ≤ 1010
- Subtask #2 (60 points) Original Constraints

-----Example-----
Input:
4
65
566
11
1623455078

Output:
A
AB

ACDFGHIJKLNPQRSTUVW

-----Explanation-----
Example case 1. Chef can pick digits 6 and 5 and create integers 56 and 65. The integer 65 corresponds to 'A'.
Example case 2. Chef can pick digits 6 and 5 and create 'A' as it equals 65. He can pick 6 and 6 (they are picked from position 2 and position 3, respectively) to create 'B' too. Hence answer is "AB".
Example case 3. It's not possible to create any character from 'A' to 'Z'. Hence, we just print a new line.
-/

def find_possible_ascii_chars (s: String) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def hasDuplicates (s: List α) : Bool :=
  sorry

theorem output_is_uppercase_ascii (input: String)
    (h: input.all (fun c => '0' ≤ c ∧ c ≤ '9')) 
    (h_size: input.length > 0) :
    let result := find_possible_ascii_chars input
    result.all (fun c => 65 ≤ c.toNat ∧ c.toNat ≤ 90) ∧ 
    ¬hasDuplicates result.data :=
  sorry

theorem chars_derive_from_input (input: String)
    (h: input.all (fun c => '0' ≤ c ∧ c ≤ '9'))
    (h_size: input.length > 0) :
    let result := find_possible_ascii_chars input
    let input_chars := input.data
    ∀ c ∈ result.data, ∃ d ∈ input_chars, d.toNat = (c.toNat / 10) + '0'.toNat :=
  sorry

theorem small_digits_give_empty (input: String)
    (h: input.all (fun c => '0' ≤ c ∧ c ≤ '4'))
    (h_size: input.length > 0) :
    find_possible_ascii_chars input = "" :=
  sorry

theorem duplicates_are_removed (input: String)
    (h: input.all (fun c => '0' ≤ c ∧ c ≤ '9'))
    (h_size: input.length > 0) :
    let result := find_possible_ascii_chars input
    ¬hasDuplicates result.data :=
  sorry

/-
info: 'A'
-/
-- #guard_msgs in
-- #eval find_possible_ascii_chars "65"

/-
info: 'AB'
-/
-- #guard_msgs in
-- #eval find_possible_ascii_chars "566"

/-
info: ''
-/
-- #guard_msgs in
-- #eval find_possible_ascii_chars "11"

-- Apps difficulty: interview
-- Assurance level: unguarded