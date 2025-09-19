-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def unlock (s : String) : String := sorry 

theorem unlock_concatenation (s1 s2 : String) : 
  unlock (s1 ++ s2) = unlock s1 ++ unlock s2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unlock_lowercase_a : unlock "a" = "2" := sorry
theorem unlock_lowercase_b : unlock "b" = "2" := sorry

theorem unlock_lowercase_c : unlock "c" = "2" := sorry

theorem unlock_lowercase_d : unlock "d" = "3" := sorry

theorem unlock_lowercase_e : unlock "e" = "3" := sorry
theorem unlock_lowercase_f : unlock "f" = "3" := sorry

theorem unlock_lowercase_g : unlock "g" = "4" := sorry
theorem unlock_lowercase_h : unlock "h" = "4" := sorry

theorem unlock_lowercase_i : unlock "i" = "4" := sorry

theorem unlock_lowercase_j : unlock "j" = "5" := sorry

theorem unlock_lowercase_k : unlock "k" = "5" := sorry
theorem unlock_lowercase_l : unlock "l" = "5" := sorry

theorem unlock_lowercase_m : unlock "m" = "6" := sorry
theorem unlock_lowercase_n : unlock "n" = "6" := sorry

theorem unlock_lowercase_o : unlock "o" = "6" := sorry

theorem unlock_lowercase_p : unlock "p" = "7" := sorry

theorem unlock_lowercase_q : unlock "q" = "7" := sorry
theorem unlock_lowercase_r : unlock "r" = "7" := sorry

theorem unlock_lowercase_s : unlock "s" = "7" := sorry

theorem unlock_lowercase_t : unlock "t" = "8" := sorry

theorem unlock_lowercase_u : unlock "u" = "8" := sorry
theorem unlock_lowercase_v : unlock "v" = "8" := sorry

theorem unlock_lowercase_w : unlock "w" = "9" := sorry
theorem unlock_lowercase_x : unlock "x" = "9" := sorry

theorem unlock_lowercase_y : unlock "y" = "9" := sorry
theorem unlock_lowercase_z : unlock "z" = "9" := sorry

theorem unlock_uppercase_a : unlock "A" = "2" := sorry
theorem unlock_uppercase_b : unlock "B" = "2" := sorry

theorem unlock_uppercase_c : unlock "C" = "2" := sorry

theorem unlock_uppercase_d : unlock "D" = "3" := sorry

theorem unlock_uppercase_e : unlock "E" = "3" := sorry
theorem unlock_uppercase_f : unlock "F" = "3" := sorry

theorem unlock_uppercase_g : unlock "G" = "4" := sorry
theorem unlock_uppercase_h : unlock "H" = "4" := sorry

theorem unlock_uppercase_i : unlock "I" = "4" := sorry

theorem unlock_uppercase_j : unlock "J" = "5" := sorry

theorem unlock_uppercase_k : unlock "K" = "5" := sorry
theorem unlock_uppercase_l : unlock "L" = "5" := sorry

theorem unlock_uppercase_m : unlock "M" = "6" := sorry
theorem unlock_uppercase_n : unlock "N" = "6" := sorry

theorem unlock_uppercase_o : unlock "O" = "6" := sorry

theorem unlock_uppercase_p : unlock "P" = "7" := sorry

theorem unlock_uppercase_q : unlock "Q" = "7" := sorry
theorem unlock_uppercase_r : unlock "R" = "7" := sorry

theorem unlock_uppercase_s : unlock "S" = "7" := sorry

theorem unlock_uppercase_t : unlock "T" = "8" := sorry

theorem unlock_uppercase_u : unlock "U" = "8" := sorry
theorem unlock_uppercase_v : unlock "V" = "8" := sorry

theorem unlock_uppercase_w : unlock "W" = "9" := sorry
theorem unlock_uppercase_x : unlock "X" = "9" := sorry

theorem unlock_uppercase_y : unlock "Y" = "9" := sorry
theorem unlock_uppercase_z : unlock "Z" = "9" := sorry
-- </vc-theorems>