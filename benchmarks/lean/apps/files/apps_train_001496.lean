/-
"I don't have any fancy quotes." - vijju123
Chef was reading some quotes by great people. Now, he is interested in classifying all the fancy quotes he knows. He thinks that all fancy quotes which contain the word "not" are Real Fancy; quotes that do not contain it are regularly fancy.
You are given some quotes. For each quote, you need to tell Chef if it is Real Fancy or just regularly fancy.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains a single string $S$ denoting a quote.

-----Output-----
For each test case, print a single line containing the string "Real Fancy" or "regularly fancy" (without quotes).

-----Constraints-----
- $1 \le T \le 50$
- $1 \le |S| \le 100$
- each character of $S$ is either a lowercase English letter or a space

-----Subtasks-----
Subtask #1 (100 points): original constraints

-----Example Input-----
2
i do not have any fancy quotes
when nothing goes right go left

-----Example Output-----
Real Fancy
regularly fancy

-----Explanation-----
Example case 1: "i do not have any fancy quotes"
Example case 2: The word "not" does not appear in the given quote.
-/

-- <vc-helpers>
-- </vc-helpers>

def classify_quotes (quote : String) : String := sorry

def splitString (s : String) : List String := sorry

theorem classify_quotes_result_valid (quote : String) :
  classify_quotes quote = "Real Fancy" ∨ classify_quotes quote = "regularly fancy" := sorry

theorem classify_quotes_not_condition (quote : String) :
  classify_quotes quote = (if (splitString quote).contains "not" then "Real Fancy" else "regularly fancy") := sorry

theorem classify_quotes_regular (quote : String) :
  ¬(splitString quote).contains "not" → classify_quotes quote = "regularly fancy" := sorry

theorem classify_quotes_all_not (n : Nat) (h : n > 0) :
  classify_quotes (String.join (List.replicate n "not" |>.intersperse " ")) = "Real Fancy" := sorry

/-
info: 'Real Fancy'
-/
-- #guard_msgs in
-- #eval classify_quotes "i do not have any fancy quotes"

/-
info: 'regularly fancy'
-/
-- #guard_msgs in
-- #eval classify_quotes "when nothing goes right go left"

/-
info: 'Real Fancy'
-/
-- #guard_msgs in
-- #eval classify_quotes "this is not fancy at all"

-- Apps difficulty: interview
-- Assurance level: unguarded