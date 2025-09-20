-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mysterious_pattern (m n : Nat) : String := sorry

-- Format properties
-- </vc-definitions>

-- <vc-theorems>
theorem valid_line_lengths {m n : Nat} (h₁ : 0 < m) (h₂ : 0 < n) :
  let lines := (mysterious_pattern m n).split (λ c => c = '\n')
  ∀ line ∈ lines, line.length ≤ m := sorry

theorem valid_num_lines {m n : Nat} (h₁ : 0 < m) (h₂ : 0 < n) :
  let lines := (mysterious_pattern m n).split (λ c => c = '\n')
  lines.length ≤ n := sorry

theorem valid_chars {m n : Nat} (h₁ : 0 < m) (h₂ : 0 < n) :
  ∀ c ∈ (mysterious_pattern m n).data,
    c = ' ' ∨ c = 'o' ∨ c = '\n' := sorry 

theorem no_trailing_spaces {m n : Nat} (h₁ : 0 < m) (h₂ : 0 < n) :
  let lines := (mysterious_pattern m n).split (λ c => c = '\n')
  ∀ line ∈ lines, line.length > 0 → line.back ≠ ' ' := sorry

-- Count properties

theorem o_count_bound {m n : Nat} (h₁ : 0 < m) (h₂ : 0 < n) :
  let s := mysterious_pattern m n
  s.data.filter (· = 'o') |>.length ≤ m := sorry

-- Basic cases

theorem minimal_case : mysterious_pattern 1 1 = "o" := sorry

-- Consistency properties  

theorem idempotent {m n : Nat} (h₁ : 0 < m) (h₂ : 0 < n) :
  mysterious_pattern m n = mysterious_pattern m n := sorry
-- </vc-theorems>