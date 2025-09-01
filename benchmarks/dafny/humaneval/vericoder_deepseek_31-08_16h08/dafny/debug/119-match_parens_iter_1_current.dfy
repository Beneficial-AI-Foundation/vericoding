function CalcBal(s: seq<int>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1, acc)
}

// <vc-helpers>
lemma CalcBalNonNegative(s: seq<int>, i: int, j: int, acc: int)
    requires 0 <= i <= j <= |s|
    requires forall k :: i <= k < j ==> s[k] == 0 || s[k] == 1
    requires acc >= 0
    requires forall k :: i <= k <= j ==> acc + CalcBal(s, i, k, 0) >= 0
    ensures CalcBal(s, i, j, acc) >= 0
{
    if i < j {
        var k := j - 1;
        calc {
            CalcBal(s, i, j, acc);
            == // def. CalcBal
            (if s[k] == 0 then 1 else -1) + CalcBal(s, i, k, acc);
            >= { CalcBalNonNegative(s, i, k, acc); }
            (if s[k] == 0 then 1 else -1);
            >= -1;
        }
    }
}

lemma CalcBalMonotonic(s: seq<int>, i: int, j: int, acc: int)
    requires 0 <= i <= j <= |s|
    requires forall k :: i <= k < j ==> s[k] == 0 || s[k] == 1
    requires acc >= 0
    ensures forall k :: i <= k <= j ==> acc + CalcBal(s, i, k, 0) >= 0
    decreases j - i
{
    if i < j {
        CalcBalMonotonic(s, i, j - 1, acc);
        var prev := CalcBal(s, i, j - 1, acc);
        assert prev >= 0 by {
            CalcBalNonNegative(s, i, j - 1, acc);
        }
        var delta := if s[j - 1] == 0 then 1 else -1;
        assert acc + CalcBal(s, i, j, 0) == acc + prev + delta;
    }
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
    var total1 := CalcBal(s1, 0, |s1|, 0);
    var i := 0;
    while i <= |s1|
        invariant 0 <= i <= |s1| + 1
        invariant forall k :: 0 <= k < i ==> CalcBal(s1, 0, k, 0) >= 0
    {
        if i < |s1| {
            CalcBalMonotonic(s1, 0, i, 0);
        }
        if i == |s1| {
            break;
        }
        var bal := CalcBal(s1, 0, i, 0);
        if bal < 0 {
            b := false;
            return;
        }
        i := i + 1;
    }
    
    i := 0;
    while i <= |s2|
        invariant 0 <= i <= |s2| + 1
        invariant forall k :: 0 <= k < i ==> total1 + CalcBal(s2, 0, k, 0) >= 0
    {
        if i < |s2| {
            CalcBalMonotonic(s2, 0, i, total1);
        }
        if i == |s2| {
            break;
        }
        var bal := total1 + CalcBal(s2, 0, i, 0);
        if bal < 0 {
            b := false;
            return;
        }
        i := i + 1;
    }
    
    b := true;
}
// </vc-code>

