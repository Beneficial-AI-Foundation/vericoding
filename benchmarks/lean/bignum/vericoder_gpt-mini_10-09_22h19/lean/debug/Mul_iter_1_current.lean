namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
def nat_to_bin_list_core : Nat → List Char → List Char
  | 0, acc => acc
  | m+1, acc => -- uses m+1 to ensure decreasing on first argument
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
  intro m
  induction m using Nat.strong_induction_on with
  | ih m =>
    intro acc
    cases m
    · -- m = 0
      simp [nat_to_bin_list_core]
    · -- m+1 case (we name n := m+1)
      let n := m+1
      have hq : n / 2 < n := by
        have : n / 2 ≤ n / 1 := Nat.div_le_div_of_le (by decide) (le_refl n)
        -- simpler: for n >= 1, n/2 < n
        apply Nat.div_lt_self (by decide)
      simp [nat_to_bin_list_core]
      let b := if n % 2 = 1 then '1' else '0'
      -- nat_to_bin_list_core n acc = nat_to_bin_list_core (n/2) (b :: acc)
      -- apply IH to (n/2) which is < n
      have ih' := ih (n / 2) (by
        apply Nat.div_lt_self (by decide))
      calc
        nat_to_bin_list_core n acc = nat_to_bin_list_core (n / 2) (b :: acc) := by simp [nat_to_bin_list_core]
        _ = (nat_to_bin_list_core (n / 2) []) ++ (b :: acc) := by
          -- apply IH for (n/2)
          have := ih (n / 2) (by apply Nat.div_lt_self; decide)
          simp at this
          exact this (b :: acc)
        _ = (nat_to_bin_list_core n []) ++ acc := by
          -- nat_to_bin_list_core n [] = nat_to_bin_list_core (n / 2) [b]
          simp [nat_to_bin_list_core]
          -- apply IH to (n/2) with acc = [b]
          have := ih (n / 2) (by apply Nat.div_lt_self; decide)
          simp at this
          calc
            (nat_to_bin_list_core (n / 2) []) ++ (b :: acc) = (nat_to_bin_list_core (n / 2) []) ++ ([b] ++ acc) := by
              simp [List.cons_append]
            _ = (nat_to_bin_list_core (n / 2) [] ++ [b]) ++ acc := by simp [List.append_assoc]

-- LLM HELPER
theorem nat_to_bin_list_spec (n : Nat) :
  Str2Int (String.mk (nat_to_bin_list n)) = n := by
  -- strong induction on n
  induction n using Nat.strong_induction_on with
  | ih n =>
    by_cases hn : n = 0
    · simp [hn, nat_to_bin_list]
      -- Str2Int of ['0'] is 0
      simp [Str2Int]
      rfl
    · -- n > 0
      simp [nat_to_bin_list, hn]
      -- let q = n / 2, b = n % 2, bchar = '1' or '0'
      let q := n / 2
      let b := n % 2
      let bchar := if b = 1 then '1' else '0'
      have hcore : nat_to_bin_list_core n [] = (nat_to_bin_list_core q []) ++ [bchar] := by
        -- nat_to_bin_list_core n [] = nat_to_bin_list_core q (bchar :: [])
        -- then apply nat_to_bin_core_append to q with acc = [bchar]
        simp [nat_to_bin_list_core]
        -- nat_to_bin_list_core n [] = nat_to_bin_list_core (n / 2) (bchar :: [])
        have : nat_to_bin_list_core (n / 2) (bchar :: []) = (nat_to_bin_list_core (n / 2) []) ++ (bchar :: []) := by
          apply nat_to_bin_core_append
        simp at this
        exact this
      -- compute Str2Int of concatenation
      have hfold := (List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bin_list_core q []) [bchar])
      -- foldl_append gives foldl f 0 (l1 ++ l2) = foldl f (foldl f 0 l1) l2
      simp [Str2Int] at hfold
      -- rewrite Str2Int (String.mk ...) using hcore and foldl_append
      have : Str2Int (String.mk ((nat_to_bin_list_core q []) ++ [bchar])) =
             (List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bin_list_core q [])) * 2 +
             (if bchar = '1' then 1 else 0) := by
        -- compute foldl over single-element list
        have := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bin_list_core q []) [bchar]
        simp [List.foldl_append] at this
        simp [List.foldl, Str2Int] at this
        -- foldl over [bchar] yields (fun acc ch => ...) applied to previous value and bchar
        have : List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bin_list_core q [])) [bchar] =
                   2 * (List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bin_list_core q [])) +
                   (if bchar = '1' then 1 else 0) := by
          simp [List.foldl]
        exact this
      -- now apply IH to q (< n)
      have q_lt : q < n := by
        apply Nat.div_lt_self
        decide
      specialize ih q q_lt
      -- ih gives Str2Int (String.mk (nat_to_bin_list q)) = q
      have hq := ih
      -- nat_to_bin_list_core q [] = nat_to_bin_list q (since q = 0 handled by previous branch inside nat_to_bin_list)
      have hq_def : nat_to_bin_list q = if q = 0 then ['0'] else nat_to_bin_list_core q [] := rfl
      -- Consider two subcases: q = 0 or q > 0. But the IH holds regardless.
      -- Use the IH result: Str2Int (String.mk (nat_to_bin_list q)) = q
      -- So foldl value for the prefix equals q
      have prefix_val : List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bin_list_core q []) = q := by
        by_cases hq0 : q = 0
        · simp [hq0, nat_to_bin_list, nat_to_bin_list_core]
          -- nat_to_bin_list_core 0 [] = []
          simp [Str2Int]
          rfl
        · -- q > 0
          have := ih q (by apply Nat.div_lt_self; decide)
          simp [nat_to_bin_list] at this
          -- nat_to_bin_list q = nat_to_bin_list_core q []
          simp [nat_to_bin_list_core] at this
          exact this
      -- compute final equality
      have final : Str2Int (String.mk ((nat_to_bin_list_core q []) ++ [bchar])) = 2 * q + (if bchar = '1' then 1 else 0) := by
        simp [Str2Int]
        -- reduce using prefix_val
        simp [prefix_val]
      -- note (if bchar = '1' then 1 else 0) = b
      have bchar_eq : (if bchar = '1' then 1 else 0) = b := by
        -- by definition bchar corresponds to b % 2
        have : b = n % 2 := rfl
        -- b is 0 or 1
        have hb : b = 0 ∨ b = 1 := by
          cases b; simp at *; try linarith; -- b is a Nat, but only 0/1 possible as remainder mod 2
          exact Or.inr rfl
        cases hb
        · -- b = 0
          subst hb
          simp [bchar]
          -- bchar = '0'
          simp
        · -- b = 1
          subst hb
          simp [bchar]
          simp
      -- now combine with arithmetic identity n = 2 * q + b
      have add_id : n = 2 * q + b := by
        -- use div_add_mod lemma: q * 2 + n % 2 = n
        have h := Nat.div_add_mod n 2
        simp [q, b] at h
        exact Eq.symm h
      -- finish
      calc
        Str2Int (String.mk (nat_to_bin_list n)) = Str2Int (String.mk ((nat_to_bin_list_core q []) ++ [bchar])) := by
          simp [nat_to_bin_list]
          exact hcore.symm
        _ = 2 * q + (if bchar = '1' then 1 else 0) := by
          exact final
        _ = 2 * q + b := by
          rw [bchar_eq]
        _ = n := by
          rw [add_comm, ← add_id]
          exact add_id
  done

-- LLM HELPER
theorem nat_to_bin_list_valid (n : Nat) : ValidBitString (String.mk (nat_to_bin_list n)) := by
  -- prove every character is '0' or '1'
  unfold ValidBitString
  intro i c h
  -- the list nat_to_bin_list only contains '0' and '1' by construction
  have : (nat_to_bin_list n).all (fun ch => ch = '0' ∨ ch = '1') := by
    -- prove by induction on n
    induction n using Nat.strong_induction_on with
    | ih n =>
      by_cases hn : n = 0
      · simp [hn, nat_to_bin_list]
        simp
      · -- n > 0
        simp [nat_to_bin_list, hn]
        -- show nat_to_bin_list_core n [] consists only of '0'/'1'
        -- prove by strong induction on the first argument of core
        have core_all : ∀ m acc, (nat_to_bin_list_core m acc).all (fun ch => ch = '0' ∨ ch = '1') := by
          intro m
          induction m using Nat.strong_induction_on with
          | ihm m =>
            intro acc
            cases m
            · simp [nat_to_bin_list_core]
            · let n' := m+1
              simp [nat_to_bin_list_core]
              let b := if n' % 2 = 1 then '1' else '0'
              have ih_use := ihm (n' / 2) (by apply Nat.div_lt_self; decide)
              have : (nat_to_bin_list_core (n' / 2) (b :: acc)).all (fun ch => ch = '0' ∨ ch = '1') := ih_use (b :: acc)
              exact this
        have := core_all n []
        exact this
  -- now use property of all to deduce element is '0' or '1'
  have lst := (nat_to_bin_list n)
  -- use List.get?_eq_some_iff_mem? We'll use simple approach: get? i = some c implies c is in list
  have mem_of_get : ∀ {i c l}, l.get? i = some c → c ∈ l := by
    intros i c l h
    apply List.get?_mem.1
    exact h
  have mem := mem_of_get (h)
  -- now from all property get membership implies property
  have all_prop := this
  have in_prop := List.mem_iff_get.2 mem
  -- Instead of the previous, use List.all_mem? Simpler:
  -- We already established all entries are '0' or '1'
  simp [List.all] at all_prop
  -- Use helper lemma: from all, any element in list satisfies predicate
  have final : c = '0' ∨ c = '1' := by
    -- use the fact that nat_to_bin_list n is finite and all elements satisfy predicate
    induction lst generalizing i c
    · cases h -- impossible: get? returns none
    · simp at all_prop
      -- we cannot directly extract by index; instead use mem argument
      have mem' := mem
      -- prove by cases on mem membership
      have : c ∈ lst := by
        exact mem
      -- from all and membership we obtain predicate holds
      have : (lst.all (fun ch => ch = '0' ∨ ch = '1')) := by
        apply (nat_to_bin_list n).all?; exact ()
      -- Actually we already have all_prop for the list
      -- Extract using List.all_mem: if all p l and a ∈ l then p a
      have p := List.all_mem.2 (by
        -- rebuild the proof: we have core_all n [] above which gave the .all result
        -- Instead of reusing, directly call nat_to_bin_list_valid using earlier core_all
        exact all_prop) this
      exact p
  exact final
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
  have prod := Str2Int s1 * Str2Int s2
  simp [Mul, nat_to_bin_string]
  -- split the conjunction using helper theorems
  apply And.intro
  · -- validity
    apply nat_to_bin_list_valid
  · -- numeric equality
    apply nat_to_bin_list_spec
-- </vc-theorem>
-- <vc-proof>
-- (The main proofs are provided above in the theorem and helper sections.)
-- No additional proofs required
-- </vc-proof>

end BignumLean