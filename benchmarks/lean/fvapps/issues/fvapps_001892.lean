-- <vc-preamble>
def CustomStack.new (maxSize : Nat) : CustomStack :=
  sorry

def CustomStack.push (s : CustomStack) (x : Int) : CustomStack :=
  sorry

def CustomStack.pop (s : CustomStack) : Int × CustomStack :=
  sorry

def CustomStack.size (s : CustomStack) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CustomStack.increment (s : CustomStack) (k : Nat) (val : Int) : CustomStack :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem stack_size_limit {maxSize : Nat} {items : List Int} (s : CustomStack) :
  s = CustomStack.new maxSize →
  (∀ x ∈ items, CustomStack.size (CustomStack.push s x) ≤ maxSize) :=
  sorry

theorem pop_empty_returns_neg_one {maxSize : Nat} (s : CustomStack) :
  s = CustomStack.new maxSize →
  CustomStack.size s = 0 →
  (CustomStack.pop s).1 = -1 :=
  sorry

theorem push_pop_single {maxSize : Nat} {val : Int} (s : CustomStack) :
  maxSize > 0 →
  s = CustomStack.new maxSize →
  (CustomStack.pop (CustomStack.push s val)).1 = val :=
  sorry

theorem empty_increment_no_effect {maxSize : Nat} (s : CustomStack) :
  s = CustomStack.new maxSize →
  CustomStack.size s = 0 →
  (CustomStack.pop (CustomStack.increment s 1 100)).1 = -1 :=
  sorry
-- </vc-theorems>