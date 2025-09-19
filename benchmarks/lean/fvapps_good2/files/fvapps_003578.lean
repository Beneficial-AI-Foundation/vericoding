-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def execute (cmd : String) : String :=
  sorry

def isValidOutput (result : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_format_valid (cmd : String) :
  isValidOutput (execute cmd) := by
  sorry

theorem empty_input_yields_asterisk (cmd : String) :
  cmd = "" → execute cmd = "*" := by
  sorry

theorem rotation_only_yields_single_point (cmd : String)
  (h : ∀ c ∈ cmd.data, c = 'R') :
  execute cmd = "*" := by
  sorry

theorem result_contains_origin (cmd : String) :
  let result := execute cmd
  result ≠ "*" →
  ∃ line, line ∈ result.splitOn "\r\n" ∧ ('*' ∈ line.data) := by
  sorry

theorem straight_line_is_continuous (cmd : String)
  (h : ∀ c ∈ cmd.data, c = 'F') :
  let result := execute cmd
  (result.data.filter (· = '*')).length = cmd.length + 1 := by
  sorry
-- </vc-theorems>