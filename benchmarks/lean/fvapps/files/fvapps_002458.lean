-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse_float_array (s : String) : List Float := sorry

theorem reverse_basic {s : String} (h: s = "1 2 3") : 
  reverse_float_array s = [3.0, 2.0, 1.0] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_negative {s : String} (h: s = "-1.5 2.5 -3.5") :
  reverse_float_array s = [-3.5, 2.5, -1.5] := sorry

theorem reverse_single {s : String} (h: s = "42") :
  reverse_float_array s = [42.0] := sorry
-- </vc-theorems>