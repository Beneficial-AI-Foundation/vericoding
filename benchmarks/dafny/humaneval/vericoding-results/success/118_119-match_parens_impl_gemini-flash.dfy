// <vc-preamble>
function CalcBal(s: seq<int>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1, acc)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes to helper, it was correct. */
function PrefixSum(s: seq<int>, k: int): int
    requires 0 <= k <= |s|
{
    CalcBal(s, 0, k, 0)
}
// </vc-helpers>

// <vc-spec>
method checkFixed(s1: seq<int>, s2: seq<int>) returns (b: bool) 

    requires forall i :: 0 <= i < |s1| ==> s1[i] == 0 || s1[i] == 1
    requires forall i :: 0 <= i < |s2| ==> s2[i] == 0 || s2[i] == 1

    ensures b ==> forall i :: 0 <= i <= |s1| ==> CalcBal(s1, 0, i, 0) >= 0
    ensures b ==> forall i :: 0 <= i <= |s2| ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) >= 0
    ensures !b ==> (exists i :: 0 <= i <= |s1| && CalcBal(s1, 0, i, 0) < 0) || (exists i :: 0 <= i <= |s2| && CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) < 0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The previous `current_balance` logic in loops was flawed. The invariant `current_balance == CalcBal(s1, 0, i, 0)` implies `current_balance` holds the balance up to `i`, but it was checked before `current_balance` was updated for `i`. The `forall k` invariant was also incorrectly structured. I've restructured the loops and invariants to correctly maintain and check the prefix sums. `current_balance` now always reflects `CalcBal(s1,0,i,0)` for the current `i` before the check `current_balance < 0` is performed. The `forall k` invariant now also reflects this. */
{
  var current_balance := 0;
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant current_balance == CalcBal(s1, 0, i, 0)
    invariant forall k :: 0 <= k < i ==> CalcBal(s1, 0, k, 0) >= 0
  {
    if current_balance < 0 {
      return false;
    }
    if i < |s1| {
      current_balance := current_balance + (if s1[i] == 0 then 1 else -1);
    }
  }

  if current_balance < 0 {
    return false;
  }

  var s1_final_balance := CalcBal(s1, 0, |s1|, 0);
  current_balance := s1_final_balance;

  for i := 0 to |s2|
    invariant 0 <= i <= |s2|
    invariant current_balance == s1_final_balance + CalcBal(s2, 0, i, 0)
    invariant forall k :: 0 <= k < i ==> s1_final_balance + CalcBal(s2, 0, k, 0) >= 0
  {
    if current_balance < 0 {
      return false;
    }
    if i < |s2| {
      current_balance := current_balance + (if s2[i] == 0 then 1 else -1);
    }
  }

  if current_balance < 0 {
    return false;
  }

  return true;
}
// </vc-code>
