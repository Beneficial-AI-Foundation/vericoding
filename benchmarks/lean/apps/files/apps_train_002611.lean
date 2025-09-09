-- <vc-helpers>
-- </vc-helpers>

def poohbear (s : String) : String := sorry

theorem empty_string :
  poohbear "" = "" := sorry

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

/-
info: 'Hello World!'
-/
-- #guard_msgs in
-- #eval poohbear "LQTcQAP>pQBBTAI-PA-PPL+P<BVPAL+T+P>PL+PBLPBP<DLLLT+P"

/-
info: '!]oo'
-/
-- #guard_msgs in
-- #eval poohbear "LLQT+P >LLLc+QIT-P AAAP P"

/-
info: '10'
-/
-- #guard_msgs in
-- #eval poohbear "++W-NE"

-- Apps difficulty: introductory
-- Assurance level: unguarded