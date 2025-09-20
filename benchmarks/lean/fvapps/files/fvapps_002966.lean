-- <vc-preamble>
def Room := (String × Nat)

def listSum : List Nat → Nat
  | [] => 0
  | x::xs => x + listSum xs

def listAll : List Nat → (Nat → Bool) → Bool
  | [], _ => true
  | x::xs, p => p x && listAll xs p
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def meeting (rooms : List Room) (need : Nat) : String ⊕ List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem meeting_zero_need {rooms : List Room} :
  meeting rooms 0 = Sum.inl "Game On" :=
sorry

theorem meeting_huge_need {rooms : List Room} {need : Nat} :
  (need > listSum (rooms.map (fun r => max (r.2 - r.1.length) 0))) →
  meeting rooms need = Sum.inl "Not enough!" :=
sorry

theorem meeting_valid_solution {rooms : List Room} {need : Nat} {result : List Nat} :
  meeting rooms need = Sum.inr result →
  (
    (result.length ≤ rooms.length) ∧
    (listAll result (fun x => x ≥ 0)) ∧
    (listSum result = need) ∧
    (rooms.zip result).all (fun p =>
      let room := p.1
      let taken := p.2
      taken ≤ max (room.2 - room.1.length) 0
    )
  ) :=
sorry
-- </vc-theorems>