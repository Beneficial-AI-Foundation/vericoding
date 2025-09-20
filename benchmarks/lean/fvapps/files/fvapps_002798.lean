-- <vc-preamble>
def sumList : List Int → Int
  | [] => 0
  | (h::t) => h + sumList t

def countList (x : Int) : List Int → Nat
  | [] => 0
  | (h::t) => (if h = x then 1 else 0) + countList x t

inductive Perm : List Int → List Int → Prop where
  | nil : Perm [] []
  | cons : (x : Int) → {l₁ l₂ : List Int} → Perm l₁ l₂ → Perm (x::l₁) (x::l₂)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def repeats (arr : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem repeats_singles {arr : List Int} (h : arr.length ≥ 1) :
  repeats arr = sumList (arr.filter (fun x => countList x arr = 1)) :=
sorry

theorem repeats_duplicate_array {arr : List Int} (h : arr.length ≥ 1) :
  repeats (arr ++ arr) = 0 :=
sorry

theorem repeats_permutation {arr₁ arr₂ : List Int}
  (h₁ : arr₁.length ≥ 2)
  (h₂ : Perm arr₁ arr₂) :
  repeats arr₁ = repeats arr₂ :=
sorry
-- </vc-theorems>