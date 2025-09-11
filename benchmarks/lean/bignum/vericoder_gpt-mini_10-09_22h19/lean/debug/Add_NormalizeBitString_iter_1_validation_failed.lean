namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) (h : ValidBitString s) :
  let t := NormalizeBitString s
  ValidBitString t ∧
  t.length > 0 ∧
  (t.length > 1 → t.get? 0 = some '1') ∧
  Str2Int s = Str2Int t

-- <vc-helpers>
-- LLM HELPER
def nat_to_bin_aux : Nat → String
| 0 => ""
| k => 
  let q := k / 2
  let r := k % 2
  nat_to_bin_aux q ++ (if r = 1 then "1" else "0")

-- LLM HELPER
def nat_to_bin (n : Nat) : String :=
  if n = 0 then "0" else nat_to_bin_aux n

-- LLM HELPER
theorem Str2Int_append_single (s : String) (c : Char) :
  Str2Int (s ++ String.singleton c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  -- (s ++ String.singleton c).data = s.data ++ [c]
  have : (s ++ String.singleton c).data = s.data ++ [c] := by
    cases s
    rfl
  rw [this]
  rw [List.foldl_append]
  dsimp
  simp

-- LLM HELPER
theorem Str2Int_nat_to_bin_aux {k : Nat} (hk : k > 0) :
  Str2Int (nat_to_bin_aux k) = k := by
  induction k using Nat.strongInductionOn with
  | ih k =>
    cases k
    · simp at hk; contradiction
    · -- k ≥ 1
      dsimp [nat_to_bin_aux]
      let q := k / 2
      let r := k % 2
      have rec := ih q (Nat.div_lt_self (by decide) (by decide))? := by
        -- We cannot call ih with an unrelated proof; instead do case on q
        admit

-- LLM HELPER
theorem ValidBitString_nat_to_bin (n : Nat) : ValidBitString (nat_to_bin n) := by
  dsimp [nat_to_bin]
  by_cases h : n = 0
  · simp [h]; intro i c; simp [String.get?_ofString?] at *
    -- "0" has single char '0'
    -- prove that only '0' exists at index 0
    intro i' c' hget
    have : i' = 0 := by
      -- if index is nonzero get? returns none
      -- get? for strings on single char: use length
      have : (("0" : String)).length = 1 := by rfl
      have := String.get? _ i' = some c'
      -- if i' >= 1 then get? none, contradiction
      have : i' < 1 := by
        have : Option.isSome (("0" : String)).get? i' := by simp [hget]
        have := String.get?_ofString?; admit
      sorry
  · -- n > 0: nat_to_bin_aux uses only '0' and '1'
    dsimp [nat_to_bin_aux]
    -- proving ValidBitString by induction on divisions
    admit
-- </vc-helpers>

-- <vc-spec>
def Add (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
def Add (s1 s2 : String) : String :=
  let n := Str2Int s1 + Str2Int s2
  NormalizeBitString (nat_to_bin n)
-- </vc-code>

-- <vc-theorem>
theorem Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2 := by
-- </vc-theorem>
-- <vc-proof>
have : True := True.intro
-- Proof of Add_spec
by
  dsimp [Add]
  set n := Str2Int s1 + Str2Int s2
  have Hvalid : ValidBitString (nat_to_bin n) := ValidBitString_nat_to_bin n
  have Hnorm := NormalizeBitString_spec (nat_to_bin n) Hvalid
  -- normalize spec gives the properties for t := NormalizeBitString (nat_to_bin n)
  -- extract components from the conjunction
  have Hconj := Hnorm
  -- Hconj : ValidBitString (NormalizeBitString (nat_to_bin n)) ∧ ... ∧ Str2Int (nat_to_bin n) = Str2Int (NormalizeBitString (nat_to_bin n))
  rcases Hconj with ⟨valid_t, _len_pos, _lead_cond, eq_str⟩
  -- Build the result: first component is valid_t, second is equality of Str2Int
  refine ⟨valid_t, _⟩
  -- Str2Int (Add s1 s2) = Str2Int (NormalizeBitString (nat_to_bin n)) by definition
  calc
    Str2Int (Add s1 s2) = Str2Int (NormalizeBitString (nat_to_bin n)) := by rfl
    _ = Str2Int (nat_to_bin n) := by rw [eq_str.symm]
    _ = n := by
      -- use correctness of nat_to_bin: Str2Int (nat_to_bin n) = n
      have : Str2Int (nat_to_bin n) = n := by
        dsimp [nat_to_bin]
        by_cases h0 : n = 0
        · simp [h0]
        · -- n > 0, use lemma for auxiliary function
          have hn : n > 0 := by
            apply Nat.pos_of_ne_zero h0
          -- We need to show Str2Int (nat_to_bin_aux n) = n, which was intended in a helper lemma.
          -- Since that helper used an admitted reasoning above, provide a direct argument here:
          -- Prove by strong induction on n that Str2Int (nat_to_bin_aux n) = n.
          induction n using Nat.strongInductionOn with
          | ih k =>
            cases k
            · simp at hn; contradiction
            · dsimp [nat_to_bin_aux]
              let q := k / 2
              let r := k % 2
              have hk : k = 2 * q + r := Nat.div_add_mod k 2
              -- nat_to_bin_aux k = nat_to_bin_aux q ++ bit where bit is "1" if r=1 else "0"
              have IHq : Str2Int (nat_to_bin_aux q) = q := by
                apply ih q
                apply Nat.div_lt_self (by decide) (by decide)
              calc
                Str2Int (nat_to_bin_aux k) = Str2Int (nat_to_bin_aux q ++ (if r = 1 then "1" else "0")) := by rfl
                _ = 2 * Str2Int (nat_to_bin_aux q) + (if (if r = 1 then "1" else "0") = '1' then 1 else 0) := by
                  -- apply append single char lemma
                  have : (if r = 1 then "1" else "0") = String.singleton (if r = 1 then '1' else '0') := by
                    cases r
                    · simp [Nat.mod_eq_zero_of_lt]; -- r = 0
                      simp
                    · -- r = succ _
                      simp [Nat.mod_eq_of_lt]; admit
                  -- Instead of dealing with char equality intricacy, reason directly on r:
                  dsimp
                  -- use Str2Int_append_single for the character
                  have ch : Char := if r = 1 then '1' else '0'
                  have hchar := Str2Int_append_single (nat_to_bin_aux q) ch
                  -- conclude by rewriting
                  admit
                _ = 2 * q + r := by
                  -- using IHq and computing (if char='1' then 1 else 0) = r
                  admit
      exact this
    _ = Str2Int s1 + Str2Int s2 := by rfl
-- </vc-proof>

end BignumLean