// <vc-preamble>
function CalcBal(s: seq<int>, i: int, j: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then 0
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed ValidPrefix with proper recursive definition */
function ValidPrefix(s: seq<int>, i: int): bool
  requires 0 <= i <= |s|
{
  if i == 0 then true
  else ValidPrefix(s, i - 1) && CalcBal(s, 0, i) >= 0
}
lemma ValidPrefixMaintainsBal(s: seq<int>, n: int)
  requires 0 <= n <= |s|
  requires n > 0
  ensures ValidPrefix(s, n - 1) ==> CalcBal(s, 0, n - 1) >= 0
{
}
// </vc-helpers>

// <vc-spec>
method correct_bracketing(s: seq<int>) returns (b: bool)

    requires forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1

    ensures (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0) ==> b
    ensures b ==> (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Simplified logic and removed problematic assertions */
{
  b := (forall i | 0 <= i <= |s| :: CalcBal(s, 0, i) >= 0);
}
// </vc-code>
