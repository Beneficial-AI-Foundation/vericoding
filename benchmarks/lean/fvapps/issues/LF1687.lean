-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def handle (f : Unit → α) (onSuccess : (Unit → α) → α → β) 
    (onFailure : (Unit → α) → Exception → β) (excType : Type) : β := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem handle_no_exception {α β : Type} [Inhabited α] [Inhabited β] {x : α} 
    (f : Unit → α) (s : (Unit → α) → α → β) (fail : (Unit → α) → Exception → β) 
    (exc : Type) (h : f = fun _ => x) :
  handle f s fail exc = s f x := sorry

theorem handle_with_failure {α β : Type} [Inhabited α] [Inhabited β] {msg : String} 
    (f : Unit → α) (s : (Unit → α) → α → β) (fail : (Unit → α) → Exception → β) :
  handle f s fail ValueError = fail f (ValueError.mk msg) := sorry

theorem handle_wrong_exception {α β : Type} [Inhabited α] [Inhabited β]
    (f : Unit → α) (s : (Unit → α) → α → β) (fail : (Unit → α) → Exception → β)
    (h : f = fun _ => default) :
  handle f s fail Exception = default := sorry

theorem handle_custom_callbacks {x : Nat}
    (f : Unit → Nat)
    (s : (Unit → Nat) → Nat → Nat) 
    (fail : (Unit → Nat) → Exception → Nat)
    (h : f = fun _ => x)
    (h₂ : s = fun _ v => 2 * v) :
  handle f s fail Exception = 2 * x := sorry
-- </vc-theorems>