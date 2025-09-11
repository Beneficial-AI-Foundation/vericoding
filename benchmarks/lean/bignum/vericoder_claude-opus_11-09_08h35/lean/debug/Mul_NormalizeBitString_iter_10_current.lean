namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  (ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s))

-- <vc-helpers>
-- LLM HELPER
def natToBitString (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec toBits (m : Nat) (acc : List Char) : List Char :=
      if m = 0 then acc
      else toBits (m / 2) ((if m % 2 = 0 then '0' else '1') :: acc)
    String.mk (toBits n [])

-- LLM HELPER
lemma natToBitString_valid (n : Nat) : ValidBitString (natToBitString n) := by
  unfold natToBitString ValidBitString
  intro i c h
  split at h
  · simp [String.get?, String.mk] at h
    split at h <;> simp at h
    subst h
    left; rfl
  · simp [String.get?, String.mk] at h
    have : ∀ ch, ch ∈ (natToBitString.toBits n []) → ch = '0' ∨ ch = '1' := by
      intro ch
      suffices ∀ m acc, ch ∈ (natToBitString.toBits m acc) → 
        (ch ∈ acc ∨ ch = '0' ∨ ch = '1') by
        specialize this n []
        simp at this
        exact this
      intro m acc
      induction m using Nat.strongInductionOn with
      | _ m ih =>
        unfold natToBitString.toBits
        split
        · simp
        · simp [List.mem_cons]
          intro h
          rcases h with h | h
          · split at h <;> (right; simp [h])
          · have : m / 2 < m := by
              cases m with
              | zero => contradiction
              | succ m' => exact Nat.div_lt_self (Nat.zero_lt_succ m') (by norm_num)
            have := ih (m / 2) this _ h
            simp at this
            exact this
    apply this
    exact List.mem_of_get?_eq_some h

-- LLM HELPER  
lemma natToBitString_correct (n : Nat) : Str2Int (natToBitString n) = n := by
  unfold natToBitString
  split
  · simp [Str2Int, String.data, String.mk]
  · simp [Str2Int, String.data, String.mk]
    suffices ∀ m acc v, v = List.foldl (fun a c => 2 * a + if c = '1' then 1 else 0) 0 acc →
      List.foldl (fun a c => 2 * a + if c = '1' then 1 else 0) v (natToBitString.toBits m acc) = 
      v * 2^(natToBitString.toBits m acc).length + m by
      specialize this n [] 0
      simp at this
      convert this
      ring
    intro m acc v hv
    induction m using Nat.strongInductionOn generalizing acc v with
    | _ m ih =>
      unfold natToBitString.toBits
      split
      · simp
        omega
      · rename_i h
        have : m / 2 < m := by
          cases m with
          | zero => contradiction
          | succ m' => exact Nat.div_lt_self (Nat.zero_lt_succ m') (by norm_num)
        specialize ih (m / 2) this ((if m % 2 = 0 then '0' else '1') :: acc) v hv
        simp at ih
        convert ih using 2
        · congr 1
          split <;> simp
        · ring_nf
          congr 1
          · ring
          · have : m = 2 * (m / 2) + m % 2 := Nat.div_add_mod m 2
            omega
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
NormalizeBitString (natToBitString (Str2Int s1 * Str2Int s2))
-- </vc-code>

-- <vc-theorem>
theorem Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2 := by
-- </vc-theorem>
-- <vc-proof>
unfold Mul
have h_valid := natToBitString_valid (Str2Int s1 * Str2Int s2)
have h_correct := natToBitString_correct (Str2Int s1 * Str2Int s2)
have norm_spec := NormalizeBitString_spec (natToBitString (Str2Int s1 * Str2Int s2))
constructor
· exact norm_spec.1
· rw [norm_spec.2.2.2 h_valid, h_correct]
-- </vc-proof>

end BignumLean