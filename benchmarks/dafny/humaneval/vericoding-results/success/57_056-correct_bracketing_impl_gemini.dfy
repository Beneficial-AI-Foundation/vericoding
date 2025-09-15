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
  b := true;
  var bal: int := 0;
  var i: int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant bal == CalcBal(s, 0, i)
    invariant b <==> (forall k :: 0 <= k <= i ==> CalcBal(s, 0, k) >= 0)
  {
    bal := bal + (if s[i] == 0 then 1 else -1);

    if b && bal < 0 {
      b := false;
    }

    i := i + 1;
  }
}
// </vc-code>
