-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decode (s : String) : String := sorry

theorem decode_involution {s : String} (h : ∀ c ∈ s.data, c.isLower) : 
  decode (decode s) = s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem decode_length_preservation {s : String} (h : ∀ c ∈ s.data, c.isLower) :
  (decode s).length = s.length := sorry

theorem decode_preserves_spaces {s : String} 
  (h : ∀ c ∈ s.data, c.isLower ∨ c = ' ') :
  s.data.countP (fun c => c = ' ') = (decode s).data.countP (fun c => c = ' ') := sorry

theorem decode_with_spacing {s : String} (n : Nat)
  (h : ∀ c ∈ s.data, c.isLower) :
  let spaced := String.mk (List.replicate n ' ' ++ s.data ++ List.replicate n ' ')
  (decode spaced).length = spaced.length ∧ 
  (decode spaced).trim = decode s := sorry
-- </vc-theorems>