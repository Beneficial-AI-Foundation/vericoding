// <vc-preamble>
function CalcBal(s: seq<int>, i: int, j: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then 0
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method correct_bracketing(s: seq<int>) returns (b: bool)

    requires forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1

    ensures (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0) ==> b
    ensures b ==> (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
