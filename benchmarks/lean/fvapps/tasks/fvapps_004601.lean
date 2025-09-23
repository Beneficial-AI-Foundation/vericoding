-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_output (cmd : String) : String := sorry

theorem pwd_returns_valid_path :
  let result := get_output "pwd"
  result.length > 0 ∧ result.contains '/' := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ls_returns_content :
  let result := get_output "ls"
  result.length > 0 := sorry

theorem basic_commands_return_nonempty (cmd : String) :
  (cmd = "ls" ∨ cmd = "pwd" ∨ cmd = "echo hello") →
  let result := get_output cmd
  result.length > 0 := sorry

theorem invalid_command_returns_empty :
  get_output "thiscommanddoesnotexist" = "" := sorry
-- </vc-theorems>