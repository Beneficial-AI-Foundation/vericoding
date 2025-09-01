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
    var balance := 0;
    var b := true;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant balance == CalcBal(s, 0, i)
        invariant forall k :: 0 <= k < i ==> CalcBal(s, 0, k) >= 0
    {
        if balance < 0 {
            b := false;
            break;
        }
        if i < |s| {
            balance := balance + (if s[i] == 0 then 1 else -1);
        }
    }
    return b;
}
// </vc-code>

