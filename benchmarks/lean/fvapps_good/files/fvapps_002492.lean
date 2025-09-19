-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def process_list_commands (commands : List String) : List String := sorry

theorem process_list_commands_result_type 
  (commands : List String) :
  let result := process_list_commands commands
  result.all (fun str => str.any (· = '[') ∧ str.any (· = ']')) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem process_list_commands_print_count
  (commands : List String) : 
  let result := process_list_commands commands
  result.length = (commands.filter (· = "print")).length :=
sorry

theorem process_list_commands_invalid_fails
  (commands : List String) :
  commands.any (fun cmd => ¬(cmd.startsWith "append" ∨ 
                            cmd.startsWith "insert" ∨
                            cmd = "print" ∨
                            cmd = "sort" ∨
                            cmd = "reverse" ∨
                            cmd = "pop")) →
  process_list_commands commands = [] :=
sorry
-- </vc-theorems>