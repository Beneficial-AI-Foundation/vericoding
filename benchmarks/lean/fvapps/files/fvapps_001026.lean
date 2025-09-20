-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_original_password (portalPass : Nat) : String := sorry

theorem portal_pass_transformation_valid (portalPass : Nat)
  (h1 : portalPass ≥ 3000)
  (h2 : portalPass ≤ 99999)
  (h3 : ∀ d : Char, d ∈ portalPass.repr.data → (d.toNat - 48) ≥ 2) :
  find_original_password portalPass =
    String.join (portalPass.repr.data.map (fun d => (Nat.repr ((d.toNat - 48 - 2))))) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem portal_pass_specific_cases :
  find_original_password 3527 = "1305" ∧
  find_original_password 47269 = "25047" ∧ 
  find_original_password 444 = "222" := sorry

theorem portal_pass_returns_string (portalPass : Nat) :
  (find_original_password portalPass).data.all (fun c => c.isDigit) := sorry
-- </vc-theorems>