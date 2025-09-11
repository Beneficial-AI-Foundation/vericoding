namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
def toBinary (m : Nat) (acc : List Char) : List Char :=
  if m = 0 then acc
  else toBinary (m / 2) ((if m % 2 = 1 then '1' else '0') :: acc)
termination_by m

-- LLM HELPER
def Nat2Str (n : Nat) : String :=
  if n = 0 then "0" else String.mk (toBinary n [])

-- LLM HELPER
lemma Nat2Str_valid (n : Nat) : ValidBitString (Nat2Str n) := by
  unfold ValidBitString Nat2Str
  split_ifs with h
  · intros i c hget
    simp only [String.get?, String.mk] at hget
    have : "0".get? i = some c := hget
    cases i with
    | mk val isLt =>
      simp [String.get?] at this
      split at this
      · injection this with heq
        left
        exact heq
      · contradiction
  · intros i c hget
    simp only [String.get?, String.mk] at hget
    suffices ∀ m acc k ch, (toBinary m acc).get? k = some ch → ch = '0' ∨ ch = '1' by
      exact this n [] i.val c hget
    clear n h hget i c
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intros acc k ch hget
      unfold toBinary at hget
      split at hget
      · assumption
      · next hnz =>
        have : m / 2 < m := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hnz) (by norm_num)
        cases k with
        | zero => 
          simp at hget
          injection hget with heq
          rw [← heq]
          split <;> simp
        | succ k' =>
          simp at hget
          exact ih (m / 2) this _ _ _ hget

-- LLM HELPER
lemma Str2Int_Nat2Str (n : Nat) : Str2Int (Nat2Str n) = n := by
  unfold Nat2Str
  split_ifs with h
  · simp [h, Str2Int, String.data, String.mk]
  · unfold Str2Int
    simp only [String.data, String.mk]
    have : ∀ m, m > 0 → (toBinary m []).foldl (fun a ch => 2 * a + (if ch = '1' then 1 else 0)) 0 = m := by
      intro m hm
      have : ∀ m acc, (toBinary m acc).foldl (fun a ch => 2 * a + (if ch = '1' then 1 else 0)) 0 = 
                     m + acc.foldl (fun a ch => 2 * a + (if ch = '1' then 1 else 0)) 0 := by
        intro m
        induction m using Nat.strong_induction_on with
        | _ m ih =>
          intro acc
          unfold toBinary
          split
          · simp
          · next hmz =>
            have hdiv : m / 2 < m := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hmz) (by norm_num)
            rw [ih (m / 2) hdiv]
            simp [List.foldl_cons]
            split
            · next hmod =>
              have : m = m / 2 * 2 + 1 := by
                rw [Nat.div_add_mod m 2]
                simp [hmod]
              linarith
            · next hmod =>
              have : m % 2 = 0 := by
                by_contra h'
                have : m % 2 < 2 := Nat.mod_lt m (by norm_num : 0 < 2)
                interval_cases m % 2
                · exact h' rfl
                · exact hmod rfl
              have : m = m / 2 * 2 := by
                rw [Nat.div_add_mod m 2, this]
                simp
              linarith
      simpa using this m (Nat.zero_lt_of_ne_zero h)
    exact this n (Nat.zero_lt_of_ne_zero h)
-- </vc-helpers>

-- <vc-spec>
def DivMod (s1 s2 : String) : (String × String) :=
-- </vc-spec>
-- <vc-code>
let n1 := Str2Int s1
  let n2 := Str2Int s2
  let q := n1 / n2
  let r := n1 % n2
  (Nat2Str q, Nat2Str r)
-- </vc-code>

-- <vc-theorem>
theorem DivMod_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2)
  (h2nz : Str2Int s2 ≠ 0) :
  let (q, r) := DivMod s1 s2
  ValidBitString q ∧ ValidBitString r ∧ Str2Int s1 = Str2Int q * Str2Int s2 + Str2Int r := by
-- </vc-theorem>
-- <vc-proof>
unfold DivMod
  simp
  constructor
  · exact Nat2Str_valid _
  constructor
  · exact Nat2Str_valid _
  · rw [Str2Int_Nat2Str, Str2Int_Nat2Str]
    exact Nat.div_add_mod (Str2Int s1) (Str2Int s2)
-- </vc-proof>

end BignumLean