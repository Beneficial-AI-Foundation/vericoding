/-
  Port of dafny-synthesis_task_id_566_SumOfDigits.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function Power10(n: nat): (r: nat)
  sorry  -- TODO: implement complex function body

def NumberToSeq (number : Int) : seq :=
  sorry  -- TODO: implement complex function body

def Sum (digits : seq<int>) : Int :=
  sorry  -- TODO: implement complex function body

def SumDigits (n : Nat) : Nat :=
  var ndigits := NumberOfDigits(n); var p := Power10(ndigits-1); SumDigitsRecursive(n, p)

function SumDigitsRecursive(n: nat, p: nat) : (r: nat)
  sorry  -- TODO: implement complex function body

function NumberOfDigits(n: nat) : (r: nat)
  if 0 ≤ n ≤ 9 then 1 else 1+NumberOfDigits(n/10)

def SumOfDigits (number : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem SumOfDigits_spec (number : Nat) (sum : Nat) :=
  (h_0 : number ≥ 0)
  : sum ≥ 0 ∧ sum == SumDigits(number)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks