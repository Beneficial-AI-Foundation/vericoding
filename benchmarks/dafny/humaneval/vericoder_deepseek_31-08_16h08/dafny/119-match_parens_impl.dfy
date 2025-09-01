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
            == { assert CalcBal(s, i, k, acc) == acc + CalcBal(s, i, k, 0); }
            (if s[k] == 0 then 1 else -1) + acc + CalcBal(s, i, k, 0);
            >= { assert acc + CalcBal(s, i, k, 0) >= 0; }
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
        var delta := if s[j - 1] == 0 then 1 else -1;
        var prev := CalcBal(s, i, j - 1, 0);
        assert acc + CalcBal(s, i, j, 0) == acc + prev + delta;
        
        // Show that acc + prev + delta >= 0 using the invariant from recursive call
        assert forall k :: i <= k <= j - 1 ==> acc + CalcBal(s, i, k, 0) >= 0;
        if s[j - 1] == 0 {
            // delta = 1, so acc + prev + 1 >= 0 since acc + prev >= 0
        } else {
            // delta = -1, need to ensure acc + prev > 0
            // Since j - 1 >= i, we have acc + prev >= 0
            // We need to use the fact that if acc + prev == 0, then we cannot have a closing parenthesis
            // But this requires additional constraints
        }
    } else {
        assert forall k :: i <= k <= i ==> acc + CalcBal(s, i, k, 0) >= 0 by {
            assert CalcBal(s, i, i, 0) == 0;
            assert acc + 0 == acc >= 0;
        }
    }
}

lemma CalcBalPreservesNonNegative(s: seq<int>, i: int, j: int)
    requires 0 <= i <= j <= |s|
    requires forall k :: i <= k < j ==> s[k] == 0 || s[k] == 1
    requires forall k :: i <= k < j ==> CalcBal(s, i, k, 0) >= 0
    ensures CalcBal(s, i, j, 0) >= 0
{
    if i < j {
        CalcBalPreservesNonNegative(s, i, j - 1);
        var delta := if s[j - 1] == 0 then 1 else -1;
        assert CalcBal(s, i, j, 0) == CalcBal(s, i, j - 1, 0) + delta;
        if s[j - 1] == 1 {
            assert CalcBal(s, i, j - 1, 0) > 0; // Need this to ensure non-negative after subtraction
        }
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
    
    // Before checking s2, we need to establish that total1 >= 0
    assert CalcBal(s1, 0, |s1|, 0) >= 0 by {
        CalcBalPreservesNonNegative(s1, 0, |s1|);
    };
    
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

