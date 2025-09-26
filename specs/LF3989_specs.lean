-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ipsubnet2list (subnet : String) : Option (List String) := sorry

def is_valid_ip_network (subnet : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ipsubnet2list_properties {a b c d : Nat} {mask : Nat} 
  (h1 : a ≤ 255) (h2 : b ≤ 255) (h3 : c ≤ 255) (h4 : d ≤ 255)
  (h5 : 24 ≤ mask) (h6 : mask ≤ 32) :
  let subnet := s!"{a}.{b}.{c}.{d}/{mask}"
  match ipsubnet2list subnet with
  | none => ¬is_valid_ip_network subnet 
  | some result => 
    is_valid_ip_network subnet ∧ 
    List.length result = 2^(32 - mask) ∧
    List.Nodup result
  := sorry

theorem ipsubnet2list_invalid_input (s : String) :
  ¬is_valid_ip_network s → 
  ipsubnet2list s = none := sorry
-- </vc-theorems>