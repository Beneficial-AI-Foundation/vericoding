namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
-- Helpers to convert Nat to binary String and basic lemmas about them.

open Std

def nat_bits_aux : Nat -> List Char
  | 0 => []
  | m => nat_bits_aux (m / 2) ++ [if m % 2 = 1 then '1' else '0']

def nat_to_bin_list (n : Nat) : List Char :=
  match n with
  | 0 => ['0']
  | _ => nat_bits_aux n

def nat_to_bin_str (n : Nat) : String :=
  String.mk (nat_to_bin_list n)

theorem nat_bits_aux_chars (m : Nat) : ∀ ch ∈ nat_bits_aux m, ch = '0' ∨ ch = '1' := by
  induction m using Nat.strong_induction_on with
  | ih m =>
    cases m
    case zero =>
      simp [nat_bits_aux]
    case succ m' =>
      -- For succ case nat_bits_aux m = nat_bits_aux (m / 2) ++ [bit]
      let bit := if (m.succ % 2 = 1) then '1' else '0'
      have : nat_bits_aux m.succ = nat_bits_aux (m.succ / 2) ++ [bit] := rfl
      intro ch h
      simp [this] at h
      rcases h with
      | inl hmem => exact (ih (m.succ / 2) (Nat.div_lt_self (by decide) (by decide)) ch hmem)
      | inr hmem => simp [hmem]; cases bit; simp_all

theorem nat_to_bin_list_chars (n : Nat) : ∀ ch ∈ nat_to_bin_list n, ch = '0' ∨ ch = '1' := by
  cases n
  case zero => simp [nat_to_bin_list]; intro ch h; simp at h; cases h; contradiction
  case succ n' =>
    simp [nat_to_bin_list]
    apply nat_bits_aux_chars

theorem Str2Int_nat_bits_aux_aux {l : List Char} :
  -- helper: Str2Int of list built by nat_bits_aux respects binary arithmetic step
  (fun ls => ls.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) l = l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := rfl
-- trivial identity to aid readability in proofs

theorem Str2Int_nat_to_bin_str (n : Nat) : Str2Int (nat_to_bin_str n) = n := by
  -- Strong induction on n, because nat_bits_aux recurses on n/2
  induction n using Nat.strong_induction_on with
  | ih n =>
    cases n
    case zero =>
      simp [nat_to_bin_str, nat_to_bin_list, Str2Int]; -- "0" => 0
      simp [String.mk]
      -- the list is ['0'], folding gives 0
      simp [List.foldl]; rfl
    case succ n' =>
      -- For positive n, nat_to_bin_list uses nat_bits_aux
      have aux_def : nat_to_bin_list (Nat.succ n') = nat_bits_aux (Nat.succ n') := by simp [nat_to_bin_list]
      simp [nat_to_bin_str, aux_def]
      -- Let bits = nat_bits_aux (succ n'), and bits = nat_bits_aux ( (succ n') / 2) ++ [b]
      let m := Nat.succ n'
      have split : nat_bits_aux m = nat_bits_aux (m / 2) ++ [if m % 2 = 1 then '1' else '0'] := rfl
      simp [split]
      -- Compute Str2Int of concatenated list: foldl over u ++ [b] equals 2 * Str2Int u + b
      set u := nat_bits_aux (m / 2) with hu
      set b := (if m % 2 = 1 then '1' else '0') with hb
      have fold_concat : (u ++ [b]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
                         2 * (u.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) +
                         (if b = '1' then 1 else 0) := by
        -- standard property of foldl for appending single element
        simp [List.foldl_append]; simp
      simp [fold_concat]
      -- By inductive hypothesis applied to m / 2 (which is smaller than m), u corresponds to m/2
      have ih_apply : (u.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) = (m / 2) := by
        apply ih (m / 2)
        apply Nat.div_lt_self; decide
      rw [ih_apply]
      -- Now use division and modulus identity: m = 2*(m/2) + m%2
      have dm := Nat.div_add_mod m 2
      -- relate (if b = '1' then 1 else 0) to m % 2
      have bit_eq : (if b = '1' then 1 else 0) = m % 2 := by
        dsimp [b]
        by_cases hodd : m % 2 = 1
        · simp [hodd]
        · have hm : m % 2 = 0 := by
            -- from hodd false, m % 2 ≠ 1; but mod 2 is either 0 or 1
            -- use mod2 properties: m % 2 ∈ {0,1}
            have : m % 2 < 2 := Nat.mod_lt _ (by decide)
            cases Nat.eq_zero_or_pos (m % 2)
            · simp [*]
            · -- if positive and <2 must be 1, contradiction, so it's zero
              have : m % 2 = 1 := by
                apply Nat.le_antisymm
                · apply Nat.le_of_lt; exact this
                · apply Nat.le_of_lt; exact this
              contradiction
          simp [hm]
        -- both branches handled
      rw [bit_eq]
      -- combine with dm
      calc
        _ = 2 * (m / 2) + m % 2 := by rfl
        _ = m := by rw [Nat.div_add_mod]; rfl

-- A lemma to assert that nat_to_bin_str produces valid bit characters only
theorem ValidBitString_of_nat_to_bin_str (n : Nat) : ValidBitString (nat_to_bin_str n) := by
  intro i c h
  -- get? for String.mk uses underlying list; nat_to_bin_list_chars gives the char restriction
  have : (nat_to_bin_str n).data.get? i = some c := by
    -- String.get? def reduces to data.get?
    exact h
  -- rewrite to list get?
  simp [nat_to_bin_str] at this
  -- now use char property of underlying list
  have ch_prop := nat_to_bin_list_chars n c this
  exact ch_prop
-- </vc-helpers>

-- <vc-spec>
def DivMod (s1 s2 : String) : (String × String) :=
-- </vc-spec>
-- <vc-code>
def DivMod (s1 s2 : String) : (String × String) :=
  let n1 := Str2Int s1
  let n2 := Str2Int s2
  let q := n1 / n2
  let r := n1 % n2
  (nat_to_bin_str q, nat_to_bin_str r)
-- </vc-code>

-- <vc-theorem>
theorem DivMod_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2)
  (h2nz : Str2Int s2 ≠ 0) :
  let (q, r) := DivMod s1 s2
  ValidBitString q ∧ ValidBitString r ∧ Str2Int s1 = Str2Int q * Str2Int s2 + Str2Int r := by
-- </vc-theorem>
-- <vc-proof>
-- Proof of the specification for DivMod
intro h
dsimp [DivMod] at h
-- Unpack q and r from the let-binding in the statement
cases h with q r
dsimp [DivMod] at q
-- Actually the structure above results in q being the pair; rewrite using definition
unfold DivMod at h
dsimp at h
-- Re-introduce names for quotient and remainder
let n1 := Str2Int s1
let n2 := Str2Int s2
let qn := n1 / n2
let rn := n1 % n2
have Hq := nat_to_bin_str qn
have Hr := nat_to_bin_str rn
-- Now prove properties
have val_q : ValidBitString Hq := ValidBitString_of_nat_to_bin_str qn
have val_r : ValidBitString Hr := ValidBitString_of_nat_to_bin_str rn
have arith : Str2Int s1 = Str2Int Hq * Str2Int s2 + Str2Int Hr := by
  -- Replace Str2Int Hq and Hr by qn and rn using the proven lemma
  have q_eq := Str2Int_nat_to_bin_str qn
  have r_eq := Str2Int_nat_to_bin_str rn
  -- compute
  calc
    Str2Int s1 = n1 := rfl
    _ = qn * n2 + rn := by
      -- definition of qn and rn
      simp [qn, rn, n1, n2]
      apply Nat.div_add_mod
    _ = Str2Int Hq * Str2Int s2 + Str2Int Hr := by
      rw [q_eq, r_eq]; rfl
-- Conclude by packaging results
exact And.intro val_q (And.intro val_r arith)
-- </vc-proof>

end BignumLean