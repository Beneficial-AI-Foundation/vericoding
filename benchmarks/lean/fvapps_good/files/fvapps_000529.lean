-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_ram_win (tr_list dr_list ts_list ds_list : List Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem can_ram_win_returns_valid_result (tr_list dr_list ts_list ds_list : List Int) :
  (can_ram_win tr_list dr_list ts_list ds_list = "yes") ∨
  (can_ram_win tr_list dr_list ts_list ds_list = "no") :=
sorry

theorem ram_wins_implies_tasks_present (tr_list dr_list ts_list ds_list : List Int) :
  can_ram_win tr_list dr_list ts_list ds_list = "yes" →
  (∀ t ∈ ts_list, t ∈ tr_list) ∧ (∀ d ∈ ds_list, d ∈ dr_list) :=
sorry

theorem ram_loses_implies_task_missing (tr_list dr_list ts_list ds_list : List Int) :
  can_ram_win tr_list dr_list ts_list ds_list = "no" →
  (∃ t ∈ ts_list, t ∉ tr_list) ∨ (∃ d ∈ ds_list, d ∉ dr_list) :=
sorry

theorem empty_required_lists_always_wins (tr_list dr_list : List Int) :
  can_ram_win tr_list dr_list [] [] = "yes" :=
sorry

theorem missing_truth_task_loses (tr_list dr_list ts_list ds_list : List Int)
  (x : Int) (h : ts_list ≠ []) (h2 : ∀ t ∈ ts_list, t < x) :
  can_ram_win tr_list dr_list (ts_list ++ [x]) ds_list = "no" :=
sorry
-- </vc-theorems>