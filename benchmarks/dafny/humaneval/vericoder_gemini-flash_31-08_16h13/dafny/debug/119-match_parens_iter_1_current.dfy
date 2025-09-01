function CalcBal(s: seq<int>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1, acc)
}

// <vc-helpers>
function CalcBal(s: seq<int>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1, acc)
}
// </vc-helpers>

// <vc-spec>
method checkFixed(s1: seq<int>, s2: seq<int>) returns (b: bool) 
    // pre-conditions-start
    requires forall i :: 0 <= i < |s1| ==> s1[i] == 0 || s1[i] == 1
    requires forall i :: 0 <= i < |s2| ==> s2[i] == 0 || s2[i] == 1
    // pre-conditions-end
    // post-conditions-start
    ensures b ==> forall i :: 0 <= i <= |s1| ==> CalcBal(s1, 0, i, 0) >= 0
    ensures b ==> forall i :: 0 <= i <= |s2| ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) >= 0
    ensures !b ==> (exists i :: 0 <= i <= |s1| && CalcBal(s1, 0, i, 0) < 0) || (exists i :: 0 <= i <= |s2| && CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) < 0)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var bal1 := 0;
    var minBal1 := 0;
    for i := 0 to |s1| - 1
        invariant 0 <= i <= |s1|
        invariant bal1 == CalcBal(s1, 0, i, 0)
        invariant minBal1 <= bal1
        invariant forall k :: 0 <= k <= i ==> CalcBal(s1, 0, k, 0) >= minBal1
    {
        if s1[i] == 0 {
            bal1 := bal1 + 1;
        } else {
            bal1 := bal1 - 1;
        }
        if bal1 < minBal1 {
            minBal1 := bal1;
        }
    }

    if minBal1 < 0 {
        return false;
    }

    var bal2 := bal1;
    var minBal2 := bal1;
    for i := 0 to |s2| - 1
        invariant 0 <= i <= |s2|
        invariant bal2 == CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0)
        invariant minBal2 <= bal2
        invariant forall k :: 0 <= k <= i ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, k, 0) >= minBal2
    {
        if s2[i] == 0 {
            bal2 := bal2 + 1;
        } else {
            bal2 := bal2 - 1;
        }
        if bal2 < minBal2 {
            minBal2 := bal2;
        }
    }

    return minBal2 >= 0;
}
// </vc-code>

