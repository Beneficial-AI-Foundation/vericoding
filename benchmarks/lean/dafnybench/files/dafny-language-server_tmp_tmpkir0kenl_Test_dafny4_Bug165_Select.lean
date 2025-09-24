-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Select {T : Type} [BEq T] (f : T → Bool) (s1 : Array T) : Array T :=
sorry

def Main {T : Type} [BEq T] (f : T → Bool) (s1 : Array T) : Unit :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Select_spec {T : Type} [BEq T] (f : T → Bool) (s1 : Array T) (r : Array T) :
(∀ e : T, f e → (s1.count e = r.count e)) ∧
(∀ e : T, ¬f e → (r.count e = 0)) :=
sorry
-- </vc-theorems>