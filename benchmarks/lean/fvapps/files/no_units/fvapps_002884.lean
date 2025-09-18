-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def interpreter (s : String) : String := sorry

theorem interpreter_empty :
  interpreter "" = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem interpreter_increment_print :
  interpreter "+*" = "\x01" := sorry

theorem interpreter_double_increment_print :
  interpreter "++*" = "\x02" := sorry

theorem interpreter_move_right_double_increment_print :
  interpreter "+>++*" = "\x02" := sorry

theorem interpreter_increment_print_move_increment_print :
  interpreter "+*>+*" = "\x01\x01" := sorry

theorem interpreter_right_triple_increment_left_increment_print :
  interpreter ">+++<+*" = "\x01" := sorry
-- </vc-theorems>