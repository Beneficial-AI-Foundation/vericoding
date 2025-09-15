// <vc-preamble>
function CalcBal(s: seq<int>, i: int, j: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then 0
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1)
}
// </vc-preamble>

// <vc-helpers>
lemma CalcBalMonotonic(s: seq<int>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= |s|
    requires forall x :: 0 <= x < |s| ==> s[x] == 0 || s[x] == 1
    ensures CalcBal(s, i, k) == CalcBal(s, i, j) + CalcBal(s, j, k)
{
    if j == k {
    } else {
        CalcBalMonotonic(s, i, j, k - 1);
    }
}
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
    var i := 0;
    while i <= |s|
        invariant 0 <= i <= |s| + 1
        invariant b ==> (forall k :: 0 <= k < i ==> CalcBal(s, 0, k) >= 0)
    {
        if i == |s| + 1 {
            break;
        }
        if CalcBal(s, 0, i) < 0 {
            b := false;
            break;
        }
        i := i + 1;
    }
}
// </vc-code>
