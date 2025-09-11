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
-- No additional helpers needed, the existing axiom Compare_spec is sufficient
-- </vc-helpers>

-- <vc-spec>
def DivMod (s1 s2 : String) : (String × String) :=
-- </vc-spec>
-- <vc-code>
let n1 := Str2Int s1
let n2 := Str2Int s2
if n2 = 0 then ("0", "0")  -- Handle division by zero case
else
  let q := n1 / n2
  let r := n1 % n2
  let rec nat2str (n : Nat) : String :=
    if n = 0 then "0"
    else
      let rec aux (m : Nat) (acc : String) : String :=
        if m = 0 then acc
        else aux (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
      aux n ""
  (nat2str q, nat2str r)
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
split_ifs with h
· contradiction
· constructor
  · -- Prove ValidBitString for q
    generalize hq : nat2str (Str2Int s1 / Str2Int s2) = q
    clear hq
    unfold ValidBitString
    intro i c hget
    generalize hn : (Str2Int s1 / Str2Int s2) = n
    clear hn
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      unfold nat2str at hget
      split_ifs at hget with hn0
      · simp at hget
        cases' String.get?_of_eq hget with k hk
        rw [hk.2]
        left
        rfl
      · generalize hacc : ("" : String) = acc at hget
        have aux_valid : ∀ m acc, (∀ i c, acc.get? i = some c → c = '0' ∨ c = '1') → 
                                   ∀ i c, (nat2str.aux m acc).get? i = some c → c = '0' ∨ c = '1' := by
          intro m
          induction m using Nat.strong_induction_on with
          | _ m IHm =>
            intro acc hvalid i c hget'
            unfold nat2str.aux at hget'
            split_ifs at hget' with hm0
            · exact hvalid i c hget'
            · apply IHm
              · exact Nat.div_lt_self (Nat.pos_of_ne_zero hm0) (by norm_num : 1 < 2)
              · intro j d hgetj
                cases' String.append_get? ((if m % 2 = 1 then "1" else "0")) acc j with hcase
                · rw [hcase] at hgetj
                  split_ifs at hgetj with hmod
                  · simp at hgetj
                    cases' String.get?_of_eq hgetj with k hk
                    rw [hk.2]
                    right
                    rfl
                  · simp at hgetj
                    cases' String.get?_of_eq hgetj with k hk
                    rw [hk.2]
                    left
                    rfl
                · rw [hcase] at hgetj
                  exact hvalid j d hgetj
              · exact hget'
        apply aux_valid
        · rw [← hacc]
          intro j d hgetj
          simp at hgetj
        · exact hget
  constructor
  · -- Prove ValidBitString for r
    generalize hr : nat2str (Str2Int s1 % Str2Int s2) = r
    clear hr
    unfold ValidBitString
    intro i c hget
    generalize hn : (Str2Int s1 % Str2Int s2) = n
    clear hn
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      unfold nat2str at hget
      split_ifs at hget with hn0
      · simp at hget
        cases' String.get?_of_eq hget with k hk
        rw [hk.2]
        left
        rfl
      · generalize hacc : ("" : String) = acc at hget
        have aux_valid : ∀ m acc, (∀ i c, acc.get? i = some c → c = '0' ∨ c = '1') → 
                                   ∀ i c, (nat2str.aux m acc).get? i = some c → c = '0' ∨ c = '1' := by
          intro m
          induction m using Nat.strong_induction_on with
          | _ m IHm =>
            intro acc hvalid i c hget'
            unfold nat2str.aux at hget'
            split_ifs at hget' with hm0
            · exact hvalid i c hget'
            · apply IHm
              · exact Nat.div_lt_self (Nat.pos_of_ne_zero hm0) (by norm_num : 1 < 2)
              · intro j d hgetj
                cases' String.append_get? ((if m % 2 = 1 then "1" else "0")) acc j with hcase
                · rw [hcase] at hgetj
                  split_ifs at hgetj with hmod
                  · simp at hgetj
                    cases' String.get?_of_eq hgetj with k hk
                    rw [hk.2]
                    right
                    rfl
                  · simp at hgetj
                    cases' String.get?_of_eq hgetj with k hk
                    rw [hk.2]
                    left
                    rfl
                · rw [hcase] at hgetj
                  exact hvalid j d hgetj
              · exact hget'
        apply aux_valid
        · rw [← hacc]
          intro j d hgetj
          simp at hgetj
        · exact hget
  · -- Prove the division equation
    have str2int_nat2str : ∀ n, Str2Int (nat2str n) = n := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n IH =>
        unfold nat2str
        split_ifs with hn0
        · rw [hn0]
          unfold Str2Int
          simp
        · generalize hacc : ("" : String) = acc
          have aux_eq : ∀ m acc k, Str2Int acc = k → Str2Int (nat2str.aux m acc) = m * 2^(acc.length) + k := by
            intro m
            induction m using Nat.strong_induction_on with
            | _ m IHm =>
              intro acc k hk
              unfold nat2str.aux
              split_ifs with hm0
              · simp [hm0, hk]
              · have hdiv_lt : m / 2 < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm0) (by norm_num : 1 < 2)
                specialize IHm (m / 2) hdiv_lt
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
                    simp [mod_zero]
                specialize IHm _ _ append_eq
                convert IHm using 1
                split_ifs with hmod <;> simp
                · have m_eq : m = m / 2 * 2 + 1 := by
                    have : m % 2 = 1 := by
                      by_contra h'
                      have : m % 2 < 2 := Nat.mod_lt m (by norm_num : 0 < 2)
                      interval_cases m % 2
                      · contradiction
                    rw [← this, Nat.div_add_mod]
                  rw [m_eq]
                  ring
                · have : m % 2 = 0 := by
                    by_contra h'
                    have : m % 2 < 2 := Nat.mod_lt m (by norm_num : 0 < 2)
                    interval_cases m % 2
                    · assumption
                    · contradiction
                  have m_eq : m = m / 2 * 2 := by
                    rw [← Nat.div_add_mod m 2, this, add_zero]
                  rw [m_eq]
                  ring
          have h1 := aux_eq n "" 0 (by simp [Str2Int])
          rw [← hacc] at h1
          simp at h1
          exact h1
    rw [str2int_nat2str, str2int_nat2str]
    exact Nat.div_add_mod (Str2Int s1) (Str2Int s2)
-- </vc-proof>

end BignumLean