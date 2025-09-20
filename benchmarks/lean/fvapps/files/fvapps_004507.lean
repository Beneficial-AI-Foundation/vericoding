-- <vc-preamble>
def List.sumLength (l: List (List α)) : Nat :=
  match l with
  | [] => 0
  | x::xs => x.length + xs.sumLength
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.hasPattern (s pattern: String) : Prop :=
sorry

def String.hasSuffix (s suffix: String) : Prop :=
sorry

def nkotb_vs_homie (reqs: List (List String)) : List String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem response_count (reqs: List (List String))
  (h1: reqs.length = 5)
  (h2: ∀ cat ∈ reqs, cat.length > 0 ∧ cat.length ≤ 5)
  : (nkotb_vs_homie reqs).length = (reqs.sumLength + 1) :=
sorry

theorem responses_end_with_homie (reqs: List (List String))
  (h1: reqs.length = 5)
  (h2: ∀ cat ∈ reqs, cat.length > 0 ∧ cat.length ≤ 5)
  (result := nkotb_vs_homie reqs)
  (i: Fin result.length)
  (h3: i.val < reqs.sumLength)
  : (result.get ⟨i.val, i.isLt⟩).hasSuffix "! Homie dont play that!" :=
sorry

theorem summary_contains_sections (reqs: List (List String))
  (h1: reqs.length = 5)
  (h2: ∀ cat ∈ reqs, cat.length > 0 ∧ cat.length ≤ 5)
  (result := nkotb_vs_homie reqs)
  (h3: reqs.sumLength < result.length)
  : let summary := result.get ⟨reqs.sumLength, h3⟩
    summary.hasPattern "monitoring objections" ∧
    summary.hasPattern "automation" ∧
    summary.hasPattern "deployment pipeline" ∧
    summary.hasPattern "cloud" ∧
    summary.hasPattern "microservices" :=
sorry

theorem empty_categories_response
  (empty_reqs: List (List String))
  (h1: empty_reqs = [[], [], [], [], []])
  : nkotb_vs_homie empty_reqs = ["0 monitoring objections, 0 automation, 0 deployment pipeline, 0 cloud, and 0 microservices."] :=
sorry
-- </vc-theorems>