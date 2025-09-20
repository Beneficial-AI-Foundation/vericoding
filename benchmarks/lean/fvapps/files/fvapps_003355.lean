-- <vc-preamble>
def get? {α : Type} (xs : List α) (i : Nat) : Option α :=
  if h : i < xs.length then some (xs.get ⟨i, h⟩) else none
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cog_RPM (cogs: List Nat) (n: Nat) : List Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_cog_property {cogs : List Nat} {n : Nat} (h : cogs.length = 1) :
  cog_RPM cogs 0 = [1, 1] :=
sorry

theorem cog_direction_property {cogs : List Nat} {n : Nat}
  (h1 : cogs.length > 1) (h2 : n < cogs.length) :
  ∃ x y : Int, cog_RPM cogs n = [x, y] ∧
  ((x > 0) ↔ (n % 2 = 0)) ∧
  ((y > 0) ↔ ((cogs.length - n) % 2 = 1)) :=
sorry

theorem cog_ratio_property {cogs : List Nat} {n : Nat}
  (h1 : cogs.length > 1) (h2 : n < cogs.length)
  (h3 : ∀ i, get? cogs i ≠ none) :
  match get? cogs n, get? cogs 0, get? cogs (cogs.length - 1) with
  | some cn, some c0, some cl =>
    ∃ x y : Int, cog_RPM cogs n = [x, y] ∧
    x.natAbs = cn / c0 ∧
    y.natAbs = cn / cl
  | _, _, _ => True :=
sorry

theorem identical_cogs_property {cogs : List Nat} {n : Nat}
  (h1 : cogs.length > 1) (h2 : n < cogs.length)
  (h3 : ∀ i j, i < cogs.length → j < cogs.length → get? cogs i = get? cogs j) :
  ∃ x y : Int, cog_RPM cogs n = [x, y] ∧
  x.natAbs = 1 ∧ y.natAbs = 1 :=
sorry
-- </vc-theorems>