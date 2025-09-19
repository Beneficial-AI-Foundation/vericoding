-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def poohbear (s : String) : String := sorry

theorem empty_string :
  poohbear "" = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_increment :
  poohbear "+N" = "1" := sorry

theorem double_increment :
  poohbear "++N" = "2" := sorry

theorem multiplication_and_addition :
  poohbear "++T+N" = "5" := sorry

theorem division :
  poohbear "+++++VN" = "2" := sorry

theorem basic_loop :
  poohbear "++W-NE" = "10" := sorry

theorem right_movement :
  poohbear ">+N" = "1" := sorry

theorem right_left_movement :
  poohbear ">+<N" = "0" := sorry
-- </vc-theorems>