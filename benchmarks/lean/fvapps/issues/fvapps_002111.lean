-- <vc-preamble>
def check_servers_alive (cmds: List Command) : List Status := sorry

theorem check_servers_alive_length (cmds: List Command) : 
  cmds.length > 0 → (check_servers_alive cmds).length = 2 := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isLive (total: Nat) (failures: Nat) : Bool :=
  total = 0 || (total - failures ≥ total / 2)
-- </vc-definitions>

-- <vc-theorems>
theorem check_servers_alive_valid_statuses (cmds: List Command) :
  cmds.length > 0 → ∀ s ∈ check_servers_alive cmds, s = Status.LIVE ∨ s = Status.DEAD := sorry

theorem check_servers_alive_server_a (cmds: List Command) (ta da: Nat) :
  ta = (cmds.filter (λ c => c.server = 1)).foldr (λ c acc => c.success + c.failure + acc) 0 →
  da = (cmds.filter (λ c => c.server = 1)).foldr (λ c acc => c.failure + acc) 0 →
  cmds.length > 0 →
  (check_servers_alive cmds)[0]! = 
    if isLive ta da then Status.LIVE else Status.DEAD := sorry

theorem check_servers_alive_server_b (cmds: List Command) (tb db: Nat) :
  tb = (cmds.filter (λ c => c.server = 2)).foldr (λ c acc => c.success + c.failure + acc) 0 →
  db = (cmds.filter (λ c => c.server = 2)).foldr (λ c acc => c.failure + acc) 0 →
  cmds.length > 0 →
  (check_servers_alive cmds)[1]! = 
    if isLive tb db then Status.LIVE else Status.DEAD := sorry

theorem check_servers_alive_all_success (n: Nat) :
  n > 0 →
  check_servers_alive [(Command.mk 1 n 0), (Command.mk 2 n 0)] = [Status.LIVE, Status.LIVE] := sorry

/-
info: ['LIVE', 'LIVE']
-/
-- #guard_msgs in
-- #eval check_servers_alive [(1, 5, 5), (2, 6, 4)]

/-
info: ['LIVE', 'DEAD']
-/
-- #guard_msgs in
-- #eval check_servers_alive [(1, 0, 10), (2, 0, 10), (1, 10, 0)]

/-
info: ['DEAD', 'DEAD']
-/
-- #guard_msgs in
-- #eval check_servers_alive [(1, 7, 3), (1, 0, 10), (1, 7, 3), (1, 1, 9), (2, 2, 8), (2, 0, 10)]
-- </vc-theorems>