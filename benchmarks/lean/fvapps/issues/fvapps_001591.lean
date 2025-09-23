-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def traverse_TCP_states : List TCPEvent → TCPState 
  | _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem traverse_TCP_states_valid (events : List TCPEvent) :
  traverse_TCP_states events ≠ TCPState.ERROR → 
  ∃ s, traverse_TCP_states events = s :=
sorry

theorem traverse_TCP_states_empty : 
  traverse_TCP_states [] = TCPState.CLOSED :=
sorry

theorem traverse_TCP_states_deterministic (events : List TCPEvent) :
  traverse_TCP_states events = traverse_TCP_states events :=
sorry

theorem traverse_TCP_states_invalid_error (events : List TCPEvent) (invalid : TCPEvent) :
  ¬(invalid ∈ events) →
  traverse_TCP_states (invalid::events) = TCPState.ERROR :=
sorry

/-
info: 'ESTABLISHED'
-/
-- #guard_msgs in
-- #eval traverse_TCP_states ["APP_PASSIVE_OPEN", "APP_SEND", "RCV_SYN_ACK"]

/-
info: 'SYN_SENT'
-/
-- #guard_msgs in
-- #eval traverse_TCP_states ["APP_ACTIVE_OPEN"]

/-
info: 'ERROR'
-/
-- #guard_msgs in
-- #eval traverse_TCP_states ["APP_ACTIVE_OPEN", "RCV_SYN_ACK", "APP_CLOSE", "RCV_FIN_ACK", "RCV_ACK"]
-- </vc-theorems>