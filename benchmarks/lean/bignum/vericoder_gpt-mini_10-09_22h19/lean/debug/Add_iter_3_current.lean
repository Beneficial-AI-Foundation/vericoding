namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
-- Helper: for m > 0 we have m / 2 < m
theorem nat_div_lt {m : Nat} (h : m > 0) : m / 2 < m := by
  cases m with
  | zero => contradiction
  | succ k =>
    -- use general lemma for division by >1
    apply Nat.div_lt_self (by decide)

-- LLM HELPER
-- Strong induction on Nat using the well-founded < relation.
theorem nat_strong_induction {P : Nat → Prop} (h : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  apply WellFounded.induction Nat.lt_wf
  intro n ih
  apply h n
  intro m hm
  apply ih m hm
-- </vc-helpers>

-- <vc-spec>
def Add (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
def nat_to_bits (n : Nat) : List Char :=
  if n = 0 then ['0']
  else
    -- build LSB-first into acc, then reverse to get MSB-first
    let rec aux : Nat → List Char → List Char
      | 0, acc => acc
      | m, acc =>
        let b := if m % 2 = 1 then '1' else '0'
        aux (m / 2) (b :: acc)
    termination_by aux _ => fun m _ => m
    decreasing_by
      -- prove m / 2 < m for recursive calls when m > 0
      apply nat_div_lt
      apply Nat.zero_lt_succ
    List.reverse (aux n [])

def bits_to_string (bits : List Char) : String :=
  String.mk bits

def nat_to_bin (n : Nat) : String :=
  bits_to_string (nat_to_bits n)

def Add (s1 s2 : String) : String :=
  let n := Str2Int s1 + Str2Int s2
  nat_to_bin n
-- </vc-code>

-- <vc-theorem>
theorem Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2 := by
  -- We'll prove property for nat_to_bin and then instantiate it with the sum.
  have bits_spec : ∀ n : Nat, (∀ {i c}, (bits_to_string (nat_to_bits n)).get? i = some c → (c = '0' ∨ c = '1')) ∧
      Str2Int (bits_to_string (nat_to_bits n)) = n := by
    apply nat_strong_induction
    intro n IH
    by_cases h0 : n = 0
    · -- n = 0
      subst h0
      simp [nat_to_bits, bits_to_string, Str2Int]
      constructor
      · intro i c hi
        simp at hi
        cases hi
        · contradiction
        injection hi with h; simp [h]; left; rfl
      · simp
    · -- n > 0
      have hn : n > 0 := by
        simp at h0; exact Nat.pos_of_ne_zero h0
      let q := n / 2
      let r := n % 2
      have nq : n = 2 * q + r := Nat.div_mod' n 2
      -- Unfold nat_to_bits to access aux
      simp [nat_to_bits]
      -- define a local aux that matches the function's aux for reasoning
      let rec aux : Nat → List Char → List Char
        | 0, acc => acc
        | m, acc => let b := if m % 2 = 1 then '1' else '0'; aux (m / 2) (b :: acc)
      termination_by aux _ => fun m _ => m
      decreasing_by
        apply nat_div_lt
        apply Nat.zero_lt_succ
      -- aux_append: aux m acc = aux m [] ++ acc
      have aux_append : ∀ m acc, aux m acc = aux m [] ++ acc := by
        apply nat_strong_induction
        intro m IHm
        intro acc
        cases m with
        | zero => simp [aux]
        | succ k =>
          simp [aux]
          let b := if (succ k) % 2 = 1 then '1' else '0'
          have hlt : (succ k) / 2 < succ k := by apply nat_div_lt; apply Nat.succ_pos
          have := IHm ((succ k) / 2) hlt
          -- apply IHm to (b :: acc)
          have step : aux ((succ k) / 2) (b :: acc) = aux ((succ k) / 2) [] ++ (b :: acc) := by
            apply IHm; assumption
          calc
            aux (succ k) acc = aux ((succ k) / 2) (b :: acc) := rfl
            _ = aux ((succ k) / 2) [] ++ (b :: acc) := step
            _ = (aux ((succ k) / 2) [] ++ [b]) ++ acc := by simp [List.append_assoc]
            _ = aux (succ k) [] ++ acc := by simp [aux]
      -- character property for aux with empty accumulator: all chars are '0' or '1'
      have aux_all_bits : ∀ m acc, List.All (fun ch => ch = '0' ∨ ch = '1') acc →
        List.All (fun ch => ch = '0' ∨ ch = '1') (aux m acc) := by
        apply nat_strong_induction
        intro m IHm
        intro acc hacc
        cases m with
        | zero => simp [aux]; exact hacc
        | succ k =>
          simp [aux]
          let b := if (succ k) %
-- </vc-theorem>
end BignumLean