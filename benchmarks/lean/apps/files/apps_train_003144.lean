-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def parity_bit (input : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem parity_bit_output_length {input : String} {part : String}
  (h : part ∈ (parity_bit input).split fun c => c = ' ') :
  part = "error" ∨ part.length = 7 :=
  sorry

theorem parity_bit_even_parity {input : String} {in_byte out_byte : String} 
  (h1 : in_byte.length = 8)
  (h2 : in_byte.all (λ c => c = '0' ∨ c = '1'))
  (h3 : out_byte ∈ (parity_bit (in_byte)).split (fun c => c = ' ')) :
  (((in_byte.toList.filter (λ c => c = '1')).length % 2 = 0 → 
    out_byte = in_byte.take 7) ∧
   ((in_byte.toList.filter (λ c => c = '1')).length % 2 = 1 → 
    out_byte = "error")) :=
  sorry

/-
info: '0101100'
-/
-- #guard_msgs in
-- #eval parity_bit "01011001"

/-
info: '0011110 error'
-/
-- #guard_msgs in
-- #eval parity_bit "00111100 00111101"

/-
info: 'error 0110000 0101011 error 0110001'
-/
-- #guard_msgs in
-- #eval parity_bit "01101110 01100000 01010110 10001111 01100011"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded