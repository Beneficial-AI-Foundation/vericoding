namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
open WellFounded

/-
Provide a basic strong_induction_on for Nat using well-founded recursion.
This recreates the common Nat.strong_induction_on facility so proofs below can use it.
-/
namespace Nat
def strong_induction_on {α : Sort _} (n : Nat) (H : ∀ m, (∀ k, k < m → α) → α) : α :=
  well_founded.fix lt_wf (fun _ => α) (fun m IH => H m (fun k hk => IH k hk)) n
end Nat

-- LLM HELPER
def nat_to_bin_list_core : Nat → List Char → List Char
  | 0, acc => acc
  | m+1, acc =>
    let n := m+1
    let b := if n % 2 = 1 then '1' else '0'
    nat_to_bin_list_core (n / 2) (b :: acc)

-- LLM HELPER
def nat_to_bin_list (n : Nat) : List Char :=
  if n = 0 then ['0'] else nat_to_bin_list_core n []

-- LLM HELPER
def nat_to_bin_string (n : Nat) : String := String.mk (nat_to_bin_list n)

-- LLM HELPER
theorem nat_to_bin_core_append :
  ∀ (m : Nat) (acc : List Char), nat_to_bin_list_core m acc = (nat_to_bin_list_core m []) ++ acc := by
  intro m acc
  -- use strong induction on m
  apply Nat.strong_induction_on m; intro m ih
  cases m with
  | zero => simp [nat_to_bin_list_core]
  | succ m =>
    let n := m + 1
    simp [nat_to_bin_list_core]
    let b := if n % 2 = 1 then '1' else '0'
    have hlt : (n / 2) < n := by
      apply Nat.div_lt_self
      decide
    -- apply IH for n/2
    have ih' := ih (n / 2) hlt
    -- nat_to_bin_list_core n acc = nat_to_bin_list_core (n/2) (b :: acc)
    -- and nat_to_bin_list_core n [] = nat_to_bin_list_core (n/2) [b]
    calc
      nat_to_bin_list_core n acc = nat_to_bin_list_core (n / 2) (b :: acc) := by simp [nat_to_bin_list_core]
      _ = (nat_to_bin_list_core (n / 2) []) ++ (b :: acc) := by
        -- apply IH' to (n/2) with accumulator (b :: acc)
        exact ih' (b :: acc)
      _ = ((nat_to_bin_list_core (n / 2) []) ++ [b]) ++ acc := by
        simp [List.append_assoc, List.cons_append]
      _ = (nat_to_bin_list_core n []) ++ acc := by
        -- nat_to_bin_list_core n [] = nat_to_bin_list_core (n / 2) [b]
        simp [nat_to_bin_list_core]
        -- apply IH' to (n/2) with acc = [b] to rewrite nat_to_bin_list_core (n / 2) [b]
        have := ih' [b]
        exact (by simp at this; exact this).symm

-- LLM HELPER
theorem nat_to_bin_list_spec (n : Nat) :
  Str2Int (String.mk (nat_to_bin_list n)) = n := by
  -- strong induction on n
  apply Nat.strong_induction_on n; intro n ih
  by_cases hn : n = 0
  · -- n = 0
    simp [hn, nat_to_bin_list, nat_to_bin_string, Str2Int]
    -- Str2Int of ['0'] is 0
    simp [List.foldl]
    rfl
  · -- n > 0
    simp [nat_to_bin_list, nat_to_bin_string, hn]
    let q := n / 2
    let b := n % 2
    let bchar := if b = 1 then '1' else '0'
    -- nat_to_bin_list_core n [] = (nat_to_bin_list_core q []) ++ [bchar]
    have hcore : nat_to_bin_list_core n [] = (nat_to_bin_list_core q []) ++ [bchar] := by
      simp [nat_to_bin_list_core]
      -- nat_to_bin_list_core n [] = nat_to_bin_list_core q (bchar :: [])
      -- now apply nat_to_bin_core_append to q with acc = [bchar]
      have : nat_to_bin_list_core q (bchar :: []) = (nat_to_bin_list_core q []) ++ (bchar :: []) := by
        exact nat_to_bin_core_append q (bchar :: [])
      simp at this
      exact this
    -- compute Str2Int of concatenation using foldl_append
    have fold_eq : Str2Int (String.mk ((nat_to_bin_list_core q []) ++ [bchar])) =
                   (List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bin_list_core q [])) * 2 +
                   (if bchar = '1' then 1 else 0) := by
      -- foldl over (l ++ [ch]) equals foldl f (foldl f 0 l) [ch] which is 2 * prefix + digit
      have := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bin_list_core q []) [bchar]
      simp [Str2Int, List.foldl] at this
      -- compute fold over single element
      simp [List.foldl] at this
      exact this
    -- apply IH to q (< n)
    have qlt : q < n := by
      apply Nat.div_lt_self
      decide
    have prefix_val : List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bin_list_core q []) = q := by
      -- use IH at q
      have ihq := ih q qlt
      -- If q = 0 then nat_to_bin_list q = ['0'] so nat_to_bin_list_core q [] = [] and foldl gives 0, which equals q.
      by_cases hq0 : q = 0
      · simp [hq0, nat_to_bin_list, nat_to_bin_list_core, Str2Int]
        rfl
      · -- q > 0: nat_to_bin_list q = nat_to_bin_list_core q []
        have := ihq
        simp [nat_to_bin_list] at this
        simp [Str2Int] at this
        -- transform Str2Int (String.mk (nat_to_bin_list_core q [])) to foldl value
        simp [Str2Int] at this
        -- the equality reduces to desired prefix_val
        exact this
    -- compute equality
    calc
      Str2Int (String.mk (nat_to_bin_list n)) = Str2Int (String.mk ((nat_to_bin_list_core q []) ++ [bchar])) := by
        simp [nat_to_bin_list]
        exact (congrArg String.mk hcore).symm
      _ = (List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bin_list_core q [])) * 2 +
          (if bchar = '1' then 1 else 0) := by
        exact fold_eq
      _ = 2 * q + (if bchar = '1' then 1 else 0) := by
        simp [prefix_val]
      _ = 2 * q + b := by
        -- show (if bchar = '1' then 1 else 0) = b
        have hb : (if bchar = '1' then 1 else 0) = b := by
          -- b is n % 2 so it's 0 or 1
          have b_range : b = 0 ∨ b = 1 := by
            cases b <;> simp [b]; try linarith; exact Or.inr rfl
          cases b_range
          · subst b_range; simp [bchar]; simp
          · subst b_range; simp [bchar]; simp
        exact hb.symm
      _ = n := by
        -- n = 2*q + b by div_add_mod
        have := Nat.div_add_mod n 2
        simp [q, b] at this
        exact this.symm

-- LLM HELPER
theorem nat_to_bin_list_valid (n : Nat) : ValidBitString (String.mk (nat_to_bin_list n)) := by
  unfold ValidBitString
  intro i c h
  -- reduce String.get? on String.mk to list.get?
  -- (String.mk l).get? = l.get? holds; use simp to unfold
  have h' : (nat_to_bin_list n).get? i = some c := by
    -- reduce the get? on String.mk
    simp [String.get?] at h
    exact h
  -- show all characters of nat_to_bin_list n are '0' or '1'
  have all_chars : (nat_to_bin_list n).all (fun ch => ch = '0' ∨ ch = '1') := by
    -- prove using strong induction on n, and an inner strong induction for core
    apply Nat.strong_induction_on n; intro n ih
    by_cases hn : n = 0
    · simp [hn, nat_to_bin_list]; simp
    · -- n > 0
      simp [nat_to_bin_list, hn]
      -- prove for core: all characters produced by nat_to_bin_list_core are '0'/'1'
      have core_all : ∀ m acc, (nat_to_bin_list_core m acc).all (fun ch => ch = '0' ∨ ch = '1') := by
        intro m
        apply Nat.strong_induction_on m; intro m ihm
        intro acc
        cases m with
        | zero => simp [nat_to_bin_list_core]
        | succ m =>
          let n' := m + 1
          simp [nat_to_bin_list_core]
          let b := if n' % 2 = 1 then '1' else '0'
          have hlt : (n' / 2) < n' := by
            apply Nat.div_lt_self; decide
          have rec := ihm (n' / 2) hlt
          -- rec provides that nat_to_bin_list_core (n'/2) (b::acc) has only '0'/'1'
          exact rec (b :: acc)
      -- apply core_all to n []
      exact core_all n []
  -- now from get? = some c derive c is in list
  have mem : c ∈ (nat_to_bin_list n) := by
    -- use List.get?_mem: l.get? i = some a -> a ∈ l
    exact List.get?_mem.1 h'
  -- from all_chars and membership deduce property
  have := List.all_mem.2 all_chars mem
  exact this
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
def Mul (s1 s2 : String) : String :=
  nat_to_bin_string (Str2Int s1 * Str2Int s2)
-- </vc-code>

-- <vc-theorem>
theorem Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2 := by
  -- Mul is defined via nat_to_bin_string on the product
  simp [Mul, nat_to_bin_string]
  apply And.intro
  · -- validity: nat_to_bin_string produces valid bitstrings for any Nat
    apply nat_to_bin_list_valid
  · -- numeric equality: nat_to_bin_string encodes numbers correctly
    apply nat_to_bin_list_spec
-- </vc-theorem>
-- <vc-proof>
-- All required proofs are provided in the helpers and theorem sections above.
-- No additional proofs required here.
-- </vc-proof>

end BignumLean