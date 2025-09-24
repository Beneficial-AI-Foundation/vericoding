-- <vc-preamble>
def ParseLines (stdin_input : String) : List String :=
  let lines := stdin_input.splitOn "\n"
  lines.filter (fun s => s.length > 0)

def FindNewline (s : String) (start : Nat) : Int :=
  let chars := s.toList
  let rec findAt (pos : Nat) : Int :=
    if pos >= chars.length then -1
    else if chars[pos]! = '\n' then pos
    else findAt (pos + 1)
  findAt start

def ValidInput (stdin_input : String) : Prop :=
  let lines := ParseLines stdin_input
  lines.length ≥ 2 ∧ lines[0]!.length > 0 ∧ lines[1]!.length > 0 ∧
  (∀ c ∈ lines[0]!.toList, 'a' ≤ c ∧ c ≤ 'z') ∧
  (∀ c ∈ lines[1]!.toList, 'a' ≤ c ∧ c ≤ 'z')

def IsSubsequence (s t : String) : Bool :=
  let rec isSubseq (s_chars t_chars : List Char) : Bool :=
    match s_chars, t_chars with
    | [], _ => true
    | _, [] => false
    | s_head :: s_tail, t_head :: t_tail =>
      if s_head = t_head then isSubseq s_tail t_tail
      else isSubseq s_chars t_tail
  isSubseq s.toList t.toList

def FilterChars (s : String) (pivot : Char) (takeLess : Bool) (takeEqual : Bool) : String :=
  let chars := s.toList
  let filtered := chars.filter (fun c =>
    (takeLess ∧ c < pivot) ∨ (takeEqual ∧ c = pivot) ∨ (¬takeLess ∧ ¬takeEqual ∧ c > pivot))
  String.mk filtered

def SortString (s : String) : String :=
  let chars := s.toList
  let sorted_chars := chars.mergeSort (fun a b => a ≤ b)
  String.mk sorted_chars

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  result ∈ ["array", "automaton", "both", "need tree"] ∧
  (let lines := ParseLines stdin_input
   let s := lines[0]!
   let t := lines[1]!
   let sx := SortString s
   let tx := SortString t
   ((sx = tx ∧ result = "array") ∨
    (sx ≠ tx ∧ IsSubsequence t s ∧ result = "automaton") ∨
    (sx ≠ tx ∧ ¬IsSubsequence t s ∧ IsSubsequence tx sx ∧ result = "both") ∨
    (sx ≠ tx ∧ ¬IsSubsequence t s ∧ ¬IsSubsequence tx sx ∧ result = "need tree")))

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>