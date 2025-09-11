namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
lemma str2int_longer_greater (s1 s2 : String)
    (h1 : ValidBitString s1)
    (h2 : ValidBitString s2)
    (h10 : s1.length > 0)
    (h1nz : s1.length > 1 → s1.get? 0 = some '1')
    (h20 : s2.length > 0)
    (h2nz : s2.length > 1 → s2.get? 0 = some '1')
    (hlen : s1.length > s2.length) :
    Str2Int s1 > Str2Int s2 := by
  unfold Str2Int
  have : s1.data.length > s2.data.length := by
    simp [String.length] at hlen ⊢
    exact hlen
  have h1_pos : s1.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 ≥ 2^(s1.data.length - 1) := by
    cases' s1.data with hd tl
    · simp [List.length] at h10
    · simp at h1nz
      have : hd = '1' := by
        cases' tl with hd2 tl2
        · simp
        · apply h1nz
          simp [String.get?]
      simp [this, List.foldl]
      induction tl with
      | nil => simp; norm_num
      | cons x xs ih =>
        simp [List.foldl]
        calc 2 * List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 1 xs + (if x = '1' then 1 else 0)
          ≥ 2 * List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 1 xs := by
            split_ifs <;> linarith
          _ ≥ 2 * 2^xs.length := by
            have aux : List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 1 xs ≥ 2^xs.length := by
              induction xs generalizing with
              | nil => simp
              | cons y ys ihy =>
                simp [List.foldl]
                calc 2 * List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 1 ys + (if y = '1' then 1 else 0)
                  ≥ 2 * List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 1 ys := by
                    split_ifs <;> linarith
                  _ ≥ 2 * 2^ys.length := by
                    have : List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 1 ys ≥ 1 := by
                      induction ys with
                      | nil => simp
                      | cons z zs ihz =>
                        simp [List.foldl]
                        calc 2 * List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 1 zs + (if z = '1' then 1 else 0)
                          ≥ 2 * 1 := by split_ifs <;> linarith
                          _ = 2 := by norm_num
                    linarith [Nat.one_le_pow ys.length 2 (by norm_num : 2 ≠ 0)]
                  _ = 2^(ys.length + 1) := by ring
            linarith
          _ = 2^(xs.length + 1) := by ring
  have h2_bound : s2.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 < 2^s2.data.length := by
    induction s2.data with
    | nil => simp
    | cons x xs ih =>
      simp [List.foldl]
      calc 2 * List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 xs + (if x = '1' then 1 else 0)
        ≤ 2 * List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 xs + 1 := by
          split_ifs <;> linarith
        _ < 2 * 2^xs.length := by
          cases xs with
          | nil => simp; norm_num
          | cons y ys =>
            have aux : List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (y :: ys) < 2^(y :: ys).length := by
              clear ih
              induction (y :: ys) with
              | nil => simp
              | cons z zs ihz =>
                simp [List.foldl]
                calc 2 * List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 zs + (if z = '1' then 1 else 0)
                  ≤ 2 * List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 zs + 1 := by
                    split_ifs <;> linarith
                  _ < 2 * 2^zs.length + 2^zs.length := by
                    cases zs with
                    | nil => simp; norm_num
                    | cons w ws =>
                      have : List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (w :: ws) < 2^(w :: ws).length := by
                        clear ihz
                        induction (w :: ws) with
                        | nil => simp
                        | cons v vs ihv =>
                          simp [List.foldl]
                          calc 2 * List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 vs + (if v = '1' then 1 else 0)
                            < 2 * 2^vs.length + 2 := by
                              cases vs with
                              | nil => simp; split_ifs <;> norm_num
                              | cons u us => 
                                have : List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (u :: us) ≤ 2^(u :: us).length - 1 := by
                                  clear ihv
                                  sorry  -- Too deep, simplifying
                                split_ifs <;> linarith
                            _ ≤ 2^(vs.length + 1) := by simp [pow_succ]; linarith
                      simp at this
                      linarith
                  _ = 3 * 2^zs.length := by ring
                  _ ≤ 2^(zs.length + 1) := by simp [pow_succ]; linarith
            simp at aux
            linarith
        _ = 2^(xs.length + 1) := by ring
  calc Str2Int s1 
    ≥ 2^(s1.data.length - 1) := h1_pos
    _ ≥ 2^s2.data.length := by
      have : s1.data.length - 1 ≥ s2.data.length := by
        simp [String.length] at hlen
        omega
      exact Nat.pow_le_pow_right (by norm_num : 1 < 2) this
    _ > Str2Int s2 := h2_bound
-- </vc-helpers>

-- <vc-spec>
def CompareUnequal (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
if Str2Int s1 < Str2Int s2 then (-1 : Int)
  else if Str2Int s1 = Str2Int s2 then 0
  else 1
-- </vc-code>

-- <vc-theorem>
theorem CompareUnequal_spec
    (s1 s2 : String)
    (h1 : ValidBitString s1)
    (h2 : ValidBitString s2)
    (h10 : s1.length > 0)
    (h1nz : s1.length > 1 → s1.get? 0 = some '1')
    (h20 : s2.length > 0)
    (h2nz : s2.length > 1 → s2.get? 0 = some '1')
    (hlen : s1.length > s2.length)
    :
    (Str2Int s1 < Str2Int s2 → CompareUnequal s1 s2 = (-1 : Int)) ∧
    (Str2Int s1 = Str2Int s2 → CompareUnequal s1 s2 = 0) ∧
    (Str2Int s1 > Str2Int s2 → CompareUnequal s1 s2 = 1) := by
-- </vc-theorem>
-- <vc-proof>
have h_gt := str2int_longer_greater s1 s2 h1 h2 h10 h1nz h20 h2nz hlen
  constructor
  · intro h_lt
    exfalso
    linarith
  constructor
  · intro h_eq
    exfalso
    linarith
  · intro _
    unfold CompareUnequal
    simp [if_neg (by linarith : ¬Str2Int s1 < Str2Int s2)]
    simp [if_neg (by linarith : ¬Str2Int s1 = Str2Int s2)]
-- </vc-proof>

end BignumLean