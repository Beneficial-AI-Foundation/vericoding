-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decipher (s : String) : String := sorry 

theorem decipher_produces_lowercase (codes : List String) 
  (h : ∀ c ∈ codes, ∃ n : Nat, n ≥ 97 ∧ n ≤ 122 ∧ c = toString n) :
  ∀ c ∈ (decipher (String.join codes)).data, c ≥ 'a' ∧ c ≤ 'z' := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem decipher_preserves_length (codes : List String)
  (h : ∀ c ∈ codes, ∃ n : Nat, n ≥ 97 ∧ n ≤ 122 ∧ c = toString n) :
  (decipher (String.join codes)).length = codes.length := sorry 

theorem decipher_maps_to_original_codes (codes : List String)
  (h : ∀ c ∈ codes, ∃ n : Nat, n ≥ 97 ∧ n ≤ 122 ∧ c = toString n)
  (i : Fin codes.length) :
  let result := decipher (String.join codes)
  Char.toNat ((result.data.get ⟨i.val, by sorry⟩)) = String.toNat! (codes.get i) := sorry

theorem decipher_round_trip (text : String)
  (h : ∀ c ∈ text.data, c ≥ 'a' ∧ c ≤ 'z') :
  decipher (String.join (text.data.map (fun c => toString (Char.toNat c)))) = text := sorry

theorem decipher_edge_cases :
  decipher "97" = "a" ∧
  decipher "122" = "z" ∧
  decipher "" = "" := sorry
-- </vc-theorems>