namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

-- <vc-helpers>
-- LLM HELPER
def nat_bits_aux : Nat -> List Char
| 0 => []
| m+1 =>
  let q := (m+1) / 2
  let r := (m+1) % 2
  (if r = 1 then '1' else '0') :: nat_bits_aux q

-- LLM HELPER
def nat_bits (n : Nat) : List Char :=
  if n = 0 then ['0'] else List.reverse (nat_bits_aux n)

-- LLM HELPER
def nat_to_bin (n : Nat) : String := String.mk (nat_bits n)

-- LLM HELPER
theorem nat_bits_aux_chars (n : Nat) :
  ∀ c ∈ (nat_bits_aux n), c = '0' ∨ c = '1' := by
  induction n with
  | zero => simp [nat_bits_aux]
  | succ m hi =>
    simp [nat_bits_aux]
    let q := (m+1) / 2
    let r := (m+1) % 2
    intro c hc
    simp at hc
    rcases hc with h | h
    · simp [h]; by_cases r = 1
      · simp [h_1]; exact Or.inr rfl
      · simp [h_1]; exact Or.inl rfl
    · apply hi; exact h

-- LLM HELPER
theorem nat_bits_chars (n : Nat) :
  ∀ c ∈ (nat_bits n), c = '0' ∨ c = '1' := by
  simp [nat_bits]
  by_cases h : n = 0
  · simp [h]; intros c hc; simp at hc; rcases hc with rfl; exact Or.inl rfl
  · simp [h]; intro c hc
    have := List.mem_reverse.1 hc
    apply nat_bits_aux_chars
    assumption

-- LLM HELPER
theorem Str2Int_nat_to_bin (n : Nat) :
  Str2Int (nat_to_bin n) = n := by
  dsimp [nat_to_bin, nat_bits]
  by_cases h0 : n = 0
  · -- n = 0 case: nat_bits 0 = ['0']
    simp [h0]
    -- Str2Int (String.mk ['0']) = foldl ... = 0
    have : String.mk ['0'] = String.mk ['0'] := rfl
    simp [Str2Int, this]
    -- compute foldl: start 0, process '0' gives 0
    rfl
  · -- n > 0 case
    have hn : n ≠ 0 := by exact h0
    -- write n as m where m > 0 to use succ form
    -- perform strong induction on n
    apply Nat.recOn n
    · intro H; contradiction
    intro m IH
    by_cases hm0 : m = 0
    · -- m = 0 handled already by h0 contradicts
      contradiction
    -- we need to show for this m (which is ≥1)
    -- use the structure of nat_bits_aux
    let aux := nat_bits_aux (m : Nat)
    have Hbits : nat_bits m = List.reverse aux := by
      simp [nat_bits, hm0]
    dsimp [Str2Int]
    -- Str2Int (String.mk (List.reverse aux)) = (List.reverse aux).foldl ...
    -- We'll show by induction on m that folding reverse aux gives m.
    -- Prove a general lemma: for all t > 0, reverse (nat_bits_aux t) foldl = t
    have key : ∀ t : Nat, 0 < t → (List.reverse (nat_bits_aux t)).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = t := by
      intro t ht
      induction' t using Nat.strong_induction_on with k IHk
      cases k
      · contradiction
      let q := k / 2
      let r := k % 2
      have q_lt : q < k := by
        have : q = k / 2 := rfl
        apply Nat.div_lt_self (Nat.pos_of_ne_zero (by decide?)) -- fallback
        simp [*] at *
      -- expand nat_bits_aux
      have : nat_bits_aux k = (if r = 1 then '1' else '0') :: nat_bits_aux q := by
        simp [nat_bits_aux]
      -- reverse of that equals reverse(nat_bits_aux q) ++ [c]
      have rev_eq : List.reverse (nat_bits_aux k) = List.reverse (nat_bits_aux q) ++ [if r = 1 then '1' else '0'] := by
        simp [this]; apply List.reverse_cons
      -- compute foldl on appended list
      rw [rev_eq, List.foldl_append]
      -- foldl over append: let A = foldl over reverse(aux q)
      set A := (List.reverse (nat_bits_aux q)).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 with hA
      -- by IH on q (q < k), we get A = q if q > 0, but q might be 0; handle both
      have Aeq : A = q := by
        by_cases hq0 : q = 0
        · -- q = 0: nat_bits_aux 0 = []
          simp [hq0, List.reverse, List.foldl, hA]
          rfl
        · apply IHk q (by
            apply Nat.div_lt_self _ (by linarith)
            exact Nat.pos_of_ne_zero hq0)
          -- IHk gives key for q: foldl reverse aux q = q
          exact (IHk q (by linarith))
      -- now continue: foldl over appended list yields (2*A + r)
      simp [hA, Aeq]
      -- final equality: 2*q + r = k
      have kl : k = 2 * q + r := by
        have : k = 2 * (k / 2) + k
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def nat_bits_aux : Nat -> List Char
| 0 => []
| m+1 =>
  let q := (m+1) / 2
  let r := (m+1) % 2
  (if r = 1 then '1' else '0') :: nat_bits_aux q

-- LLM HELPER
def nat_bits (n : Nat) : List Char :=
  if n = 0 then ['0'] else List.reverse (nat_bits_aux n)

-- LLM HELPER
def nat_to_bin (n : Nat) : String := String.mk (nat_bits n)

-- LLM HELPER
theorem nat_bits_aux_chars (n : Nat) :
  ∀ c ∈ (nat_bits_aux n), c = '0' ∨ c = '1' := by
  induction n with
  | zero => simp [nat_bits_aux]
  | succ m hi =>
    simp [nat_bits_aux]
    let q := (m+1) / 2
    let r := (m+1) % 2
    intro c hc
    simp at hc
    rcases hc with h | h
    · simp [h]; by_cases r = 1
      · simp [h_1]; exact Or.inr rfl
      · simp [h_1]; exact Or.inl rfl
    · apply hi; exact h

-- LLM HELPER
theorem nat_bits_chars (n : Nat) :
  ∀ c ∈ (nat_bits n), c = '0' ∨ c = '1' := by
  simp [nat_bits]
  by_cases h : n = 0
  · simp [h]; intros c hc; simp at hc; rcases hc with rfl; exact Or.inl rfl
  · simp [h]; intro c hc
    have := List.mem_reverse.1 hc
    apply nat_bits_aux_chars
    assumption

-- LLM HELPER
theorem Str2Int_nat_to_bin (n : Nat) :
  Str2Int (nat_to_bin n) = n := by
  dsimp [nat_to_bin, nat_bits]
  by_cases h0 : n = 0
  · -- n = 0 case: nat_bits 0 = ['0']
    simp [h0]
    -- Str2Int (String.mk ['0']) = foldl ... = 0
    have : String.mk ['0'] = String.mk ['0'] := rfl
    simp [Str2Int, this]
    -- compute foldl: start 0, process '0' gives 0
    rfl
  · -- n > 0 case
    have hn : n ≠ 0 := by exact h0
    -- write n as m where m > 0 to use succ form
    -- perform strong induction on n
    apply Nat.recOn n
    · intro H; contradiction
    intro m IH
    by_cases hm0 : m = 0
    · -- m = 0 handled already by h0 contradicts
      contradiction
    -- we need to show for this m (which is ≥1)
    -- use the structure of nat_bits_aux
    let aux := nat_bits_aux (m : Nat)
    have Hbits : nat_bits m = List.reverse aux := by
      simp [nat_bits, hm0]
    dsimp [Str2Int]
    -- Str2Int (String.mk (List.reverse aux)) = (List.reverse aux).foldl ...
    -- We'll show by induction on m that folding reverse aux gives m.
    -- Prove a general lemma: for all t > 0, reverse (nat_bits_aux t) foldl = t
    have key : ∀ t : Nat, 0 < t → (List.reverse (nat_bits_aux t)).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = t := by
      intro t ht
      induction' t using Nat.strong_induction_on with k IHk
      cases k
      · contradiction
      let q := k / 2
      let r := k % 2
      have q_lt : q < k := by
        have : q = k / 2 := rfl
        apply Nat.div_lt_self (Nat.pos_of_ne_zero (by decide?)) -- fallback
        simp [*] at *
      -- expand nat_bits_aux
      have : nat_bits_aux k = (if r = 1 then '1' else '0') :: nat_bits_aux q := by
        simp [nat_bits_aux]
      -- reverse of that equals reverse(nat_bits_aux q) ++ [c]
      have rev_eq : List.reverse (nat_bits_aux k) = List.reverse (nat_bits_aux q) ++ [if r = 1 then '1' else '0'] := by
        simp [this]; apply List.reverse_cons
      -- compute foldl on appended list
      rw [rev_eq, List.foldl_append]
      -- foldl over append: let A = foldl over reverse(aux q)
      set A := (List.reverse (nat_bits_aux q)).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 with hA
      -- by IH on q (q < k), we get A = q if q > 0, but q might be 0; handle both
      have Aeq : A = q := by
        by_cases hq0 : q = 0
        · -- q = 0: nat_bits_aux 0 = []
          simp [hq0, List.reverse, List.foldl, hA]
          rfl
        · apply IHk q (by
            apply Nat.div_lt_self _ (by linarith)
            exact Nat.pos_of_ne_zero hq0)
          -- IHk gives key for q: foldl reverse aux q = q
          exact (IHk q (by linarith))
      -- now continue: foldl over appended list yields (2*A + r)
      simp [hA, Aeq]
      -- final equality: 2*q + r = k
      have kl : k = 2 * q + r := by
        have : k = 2 * (k / 2) + k
-- </vc-code>

end BignumLean