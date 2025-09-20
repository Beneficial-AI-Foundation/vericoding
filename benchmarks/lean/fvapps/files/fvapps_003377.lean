-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def around_fib (n : Nat) : String := sorry

theorem around_fib_result_format (n : Nat) (h : n ≤ 1000) : 
  let result := around_fib n
  ∃ last_chunk max_count max_digit, 
    String.startsWith result "Last chunk " ∧
    result.any (fun c => c = ';') ∧
    String.length result > 0 ∧
    0 ≤ max_digit ∧ max_digit ≤ 9 ∧
    max_count > 0 ∧
    String.length last_chunk ≤ 25 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem around_fib_string_properties (n : Nat) (h : n ≤ 100) :
  let result := around_fib n
  let parts := String.split result (· == ';')
  let lastChunk := (String.split (parts.head!) (· == ' ')).getLast!
  ∃ maxCount : Nat,
    maxCount > 0 ∧
    (parts.length = 2) ∧
    String.any result (· == ';') ∧
    String.any result (· == 'f') := sorry
-- </vc-theorems>