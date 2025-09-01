function CalcBal(s: seq<int>, i: int, j: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then 0
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method correct_bracketing(s: seq<int>) returns (b: bool)
    // pre-conditions-start
    requires forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
    // pre-conditions-end
    // post-conditions-start
    ensures (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0) ==> b
    ensures b ==> (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var bal := 0;
  var k := 0;
  while k < |s|
    invariant 0 <= k <= |s|
    invariant bal == CalcBal(s, 0, k)
    invariant bal >= 0
    invariant forall m :: 0 <= m <= k ==> CalcBal(s, 0, m) >= 0
  {
    if s[k] == 0 {
      bal := bal + 1;
    } else {
      bal := bal - 1;
    }
    if bal < 0 {
      return false;
    }
    k := k + 1;
  }
  return true;
}
// </vc-code>

