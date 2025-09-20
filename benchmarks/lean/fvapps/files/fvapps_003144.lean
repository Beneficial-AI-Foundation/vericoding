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
-- </vc-theorems>