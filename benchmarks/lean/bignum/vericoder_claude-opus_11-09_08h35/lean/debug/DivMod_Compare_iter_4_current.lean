namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Compare (s1 s2 : String) : Int :=
  sorry

axiom Compare_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  (Str2Int s1 < Str2Int s2 → Compare s1 s2 = (-1 : Int)) ∧
  (Str2Int s1 = Str2Int s2 → Compare s1 s2 = 0) ∧
  (Str2Int s1 > Str2Int s2 → Compare s1 s2 = 1)

-- <vc-helpers>
-- LLM HELPER
def Nat2Str (n : Nat) : String :=
  if n = 0 then "0" else
    let rec aux (m : Nat) (acc : String) : String :=
      if m = 0 then acc
      else aux (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
    aux n ""

-- LLM HELPER
lemma Nat2Str_valid (n : Nat) : ValidBitString (Nat2Str n) := by
  unfold Nat2Str ValidBitString
  split_ifs with h
  · intros i c hget
    simp at hget
    cases' String.get?_of_eq hget with k hk
    rw [hk.2]
    simp
    left; rfl
  · generalize hacc : ("" : String) = acc
    have aux_valid : ∀ m acc, ValidBitString acc → ValidBitString (Nat2Str.aux m acc) := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m IH =>
        intro acc hvalid
        unfold Nat2Str.aux
        split_ifs with hm
        · exact hvalid
        · apply IH
          · exact Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num : 1 < 2)
          · intros i c hget
            cases' String.append_get? ((if m % 2 = 1 then "1" else "0")) acc i with hcase
            · rw [hcase] at hget
              split_ifs at hget with hmod
              · simp at hget
                cases' String.get?_of_eq hget with k hk
                rw [hk.2]
                simp
                right; rfl
              · simp at hget
                cases' String.get?_of_eq hget with k hk
                rw [hk.2]
                simp
                left; rfl
            · rw [hcase] at hget
              exact hvalid hget
    apply aux_valid
    rw [← hacc]
    intros i c hget
    simp at hget

-- LLM HELPER
lemma Str2Int_Nat2Str (n : Nat) : Str2Int (Nat2Str n) = n := by
  unfold Nat2Str
  split_ifs with h
  · rw [h]
    unfold Str2Int
    simp
  · generalize hacc : ("" : String) = acc
    generalize hn' : n = n'
    rw [← hn']
    clear hn' h
    have aux_eq : ∀ m acc k, Str2Int acc = k → Str2Int (Nat2Str.aux m acc) = m * 2^(acc.length) + k := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m IH =>
        intro acc k hk
        unfold Nat2Str.aux
        split_ifs with hm
        · simp [hm, hk]
        · have hdiv_lt : m / 2 < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num : 1 < 2)
          specialize IH (m / 2) hdiv_lt
          have append_eq : Str2Int ((if m % 2 = 1 then "1" else "0") ++ acc) = m % 2 * 2^acc.length + k := by
            unfold Str2Int
            split_ifs with hmod
            · simp [List.foldl_append, hk]
              ring
            · simp [List.foldl_append, hk]
              have mod_zero : m % 2 = 0 := by
                by_contra h'
                have : m % 2 < 2 := Nat.mod_lt m (by norm_num : 0 < 2)
                interval_cases m % 2
                · assumption
                · contradiction
              simp [mod_zero]
          specialize IH _ _ append_eq
          convert IH using 1
          split_ifs with hmod <;> simp
          · have m_eq : m = m / 2 * 2 + 1 := by
              have mod_one : m % 2 = 1 := by
                by_contra h'
                have : m % 2 < 2 := Nat.mod_lt m (by norm_num : 0 < 2)
                interval_cases m % 2
                · contradiction
                · assumption
              rw [← mod_one, Nat.div_add_mod]
            rw [m_eq]
            ring
          · have mod_zero : m % 2 = 0 := by
              by_contra h'
              have : m % 2 < 2 := Nat.mod_lt m (by norm_num : 0 < 2)
              interval_cases m % 2
              · assumption
              · contradiction
            have m_eq : m = m / 2 * 2 := by
              rw [← Nat.div_add_mod m 2, mod_zero, add_zero]
            rw [m_eq]
            ring
    have h1 := aux_eq n' "" 0 (by simp [Str2Int])
    rw [← hacc] at h1
    simp at h1
    exact h1

-- LLM HELPER
def Compare_impl (s1 s2 : String) : Int :=
  let n1 := Str2Int s1
  let n2 := Str2Int s2
  if n1 < n2 then -1
  else if n1 = n2 then 0
  else 1
-- </vc-helpers>

-- <vc-spec>
def DivMod (s1 s2 : String) : (String × String) :=
-- </vc-spec>
-- <vc-code>
let n1 := Str2Int s1
let n2 := Str2Int s2
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
simp
constructor
· exact Nat2Str_valid _
constructor
· exact Nat2Str_valid _
· rw [Str2Int_Nat2Str, Str2Int_Nat2Str]
  exact Nat.div_add_mod (Str2Int s1) (Str2Int s2)
-- </vc-proof>

end BignumLean