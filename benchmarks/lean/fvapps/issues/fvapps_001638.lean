-- <vc-preamble>
def sum (l: List Int) : Int :=
  match l with
  | [] => 0
  | h::t => h + sum t

def prod (l: List Int) : Int :=
  match l with
  | [] => 1
  | h::t => h * prod t

def bitAnd (l: List Int) : Int :=
  match l with
  | [] => 0
  | [x] => x
  | h::t => h

structure CPU where
  regs : String → Int
  stack : List Int

structure Machine where
  cpu : CPU
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Machine.execute : Machine → String → Machine :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arithmetic_operations_stack_add 
  (values : List Int) 
  (h : values.length ≥ 2 ∧ values.length ≤ 10) :
  let m : Machine := ⟨⟨λ_ => 0, []⟩⟩
  let m' := (values.foldl (λ acc v => Machine.execute acc s!"push {v}") m)
  let m'' := Machine.execute m' s!"add {values.length}"
  m''.cpu.regs "a" = values.sum := 
  sorry

theorem arithmetic_operations_stack_mul 
  (values : List Int)
  (h : values.length ≥ 2 ∧ values.length ≤ 10) :
  let m : Machine := ⟨⟨λ_ => 0, []⟩⟩
  let m' := (values.foldl (λ acc v => Machine.execute acc s!"push {v}") m)
  let m'' := Machine.execute m' s!"mul {values.length}"
  m''.cpu.regs "a" = values.prod :=
  sorry

theorem arithmetic_operations_stack_and
  (values : List Int)
  (h : values.length ≥ 2 ∧ values.length ≤ 10) :
  let m : Machine := ⟨⟨λ_ => 0, []⟩⟩
  let m' := (values.foldl (λ acc v => Machine.execute acc s!"push {v}") m)
  let m'' := Machine.execute m' s!"and {values.length}"
  m''.cpu.regs "a" = values.bitAnd :=
  sorry

theorem register_operations_mov
  (reg : String)
  (value : Int)
  (h : reg ∈ ["a", "b", "c", "d"]) :
  let m : Machine := ⟨⟨λ_ => 0, []⟩⟩
  let m' := Machine.execute m s!"mov {value}, {reg}"
  m'.cpu.regs reg = value :=
  sorry

theorem register_operations_push_pop
  (reg : String)
  (value : Int)
  (h : reg ∈ ["a", "b", "c", "d"]) :
  let m : Machine := ⟨⟨λ_ => 0, []⟩⟩
  let m' := Machine.execute m s!"mov {value}, {reg}"
  let m'' := Machine.execute m' s!"push {m'.cpu.regs reg}"
  let m''' := Machine.execute m'' "pop a"
  m'''.cpu.regs "a" = value :=
  sorry
-- </vc-theorems>