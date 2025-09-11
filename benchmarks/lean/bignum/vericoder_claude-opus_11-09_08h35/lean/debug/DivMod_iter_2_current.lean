namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
def Nat2Str (n : Nat) : String :=
  if n = 0 then "0" else
    let rec toBinary (m : Nat) (acc : List Char) : List Char :=
      if m = 0 then acc
      else toBinary (m / 2) ((if m % 2 = 1 then '1' else '0') :: acc)
    ⟨toBinary n []⟩

-- LLM HELPER
lemma Nat2Str_valid (n : Nat) : ValidBitString (Nat2Str n) := by
  unfold ValidBitString Nat2Str
  split_ifs with h
  · intros i c hget
    simp only [String.get?] at hget
    split at hget <;> simp at hget
    next h' => 
      simp [List.get?] at hget
      split at hget <;> simp at hget
      injection hget with heq
      rw [← heq]
      left; rfl
  · intros i c hget
    simp only [String.get?] at hget
    split at hget <;> simp at hget
    next h' =>
      generalize hlist : (Nat2Str.toBinary n []) = l
      rw [hlist] at hget
      clear hlist
      suffices ∀ l acc i c, (Nat2Str.toBinary l acc).get? i = some c → c = '0' ∨ c = '1'
        from this n [] i.val c hget
      clear n h h' hget i c
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intros acc i c hget
        unfold Nat2Str.toBinary at hget
        split at hget
        · simp at hget
        · next hnz =>
          have : n / 2 < n := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hnz) (by norm_num)
          exact ih (n / 2) this _ _ _ hget

-- LLM HELPER  
lemma Str2Int_Nat2Str (n : Nat) : Str2Int (Nat2Str n) = n := by
  unfold Nat2Str
  split_ifs with h
  · simp [h, Str2Int, String.data]
  · unfold Str2Int
    simp only [String.data]
    suffices ∀ m acc, (Nat2Str.toBinary m acc).foldl (fun a ch => 2 * a + (if ch = '1' then 1 else 0)) 0 = 
                       m + acc.foldl (fun a ch => 2 * a + (if ch = '1' then 1 else 0)) 0
      by simpa using this n []
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro acc
      unfold Nat2Str.toBinary
      split
      · simp
      · next hmz =>
        have hdiv : m / 2 < m := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hmz) (by norm_num)
        rw [ih (m / 2) hdiv]
        simp [List.foldl_cons]
        split <;> simp
        · have : m % 2 = 1 := by simp at *; exact this
          rw [Nat.div_add_mod m 2]
          ring
        · have : m % 2 = 0 := by
            by_contra h'
            have : m % 2 < 2 := Nat.mod_lt m (by norm_num)
            interval_cases m % 2
            · assumption
            · simp at h
          rw [Nat.div_add_mod m 2, this]
          ring
-- </vc-helpers>

-- <vc-spec>
def DivMod (s1 s2 : String) : (String × String) :=
-- </vc-spec>
-- <vc-code>
let n1 := Str2Int s1
  let n2 := Str2Int s2
  if n2 = 0 then
    (s1, "0")  -- Arbitrary behavior when dividing by zero
  else
    (Nat2Str (n1 / n2), Nat2Str (n1 % n2))
-- </vc-code>

-- <vc-theorem>
theorem DivMod_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2)
  (h2nz : Str2Int s2 ≠ 0) :
  let (q, r) := DivMod s1 s2
  ValidBitString q ∧ ValidBitString r ∧ Str2Int s1 = Str2Int q * Str2Int s2 + Str2Int r := by
-- </vc-theorem>
-- <vc-proof>
unfold DivMod
  simp only
  split_ifs with heq
  · contradiction
  · constructor
    · apply Nat2Str_valid
    · constructor
      · apply Nat2Str_valid
      · rw [Str2Int_Nat2Str, Str2Int_Nat2Str]
        exact Nat.div_add_mod (Str2Int s1) (Str2Int s2)
-- </vc-proof>

end BignumLean