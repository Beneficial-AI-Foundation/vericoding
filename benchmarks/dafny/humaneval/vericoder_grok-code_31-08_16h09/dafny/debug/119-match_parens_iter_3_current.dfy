function CalcBal(s: seq<int>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1, acc)
}

// <vc-helpers>
// No updates needed
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
    var bal := 0;
    var i := 0;
    b := true;
    while i < |s1|
        invariant 0 <= i <= |s1|
        invariant bal == CalcBal(s1, 0, i, 0)
        invariant b ==> forall k :: 0 <= k < i ==> CalcBal(s1, 0, k+1, 0) >= 0
    {
        var a := (if s1[i] == 0 then 1 else -1);
        bal := bal + a;
        if bal < 0 {
            b := false;
        }
        i := i + 1;
    }
    var j := 0;
    while j < |s2|
        invariant 0 <= j <= |s2|
        invariant bal == CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, j, 0)
        invariant b ==> forall k :: 0 <= k < j ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, k+1, 0) >= 0
    {
        var a := (if s2[j] == 0 then 1 else -1);
        bal := bal + a;
        if bal < 0 {
            b := false;
        }
        j := j + 1;
    }
    return b;
}
// </vc-code>

