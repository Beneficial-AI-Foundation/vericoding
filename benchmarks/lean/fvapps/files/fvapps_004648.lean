-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def collatz (n : Nat) : String := sorry

theorem collatz_returns_string (n : Nat) : 
  n > 0 → collatz n ≠ "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem collatz_steps_are_digits (n : Nat) (s : String) :
  n > 0 → s ∈ (collatz n).splitOn "->" → 
  ∀ c ∈ s.data, c.isDigit := sorry

theorem collatz_starts_with_input (n : Nat) :
  n > 0 → ((collatz n).splitOn "->").get! 0 = toString n := sorry

theorem collatz_ends_with_one (n : Nat) :
  n > 0 → ((collatz n).splitOn "->").getLast! = "1" := sorry

theorem collatz_follows_rules (n : Nat) (i : Nat) :
  n > 0 → i < ((collatz n).splitOn "->").length - 1 →
  let nums := (collatz n).splitOn "->"
  let cur := String.toNat! (nums.get! i)
  let next := String.toNat! (nums.get! (i+1))
  if cur % 2 = 0 
  then next = cur / 2
  else next = 3 * cur + 1 := sorry
-- </vc-theorems>