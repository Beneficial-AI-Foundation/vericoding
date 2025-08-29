function CalcBal(s: seq<int>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1, acc)
}

// <vc-helpers>
lemma CalcBalAppend(s: seq<int>, i: int, j: int, acc: int)
    requires 0 <= i <= j <= |s|
    ensures CalcBal(s, i, j, acc) == acc + CalcBal(s, i, j, 0)
{
    if i == j {
        assert CalcBal(s, i, j, acc) == acc;
        assert CalcBal(s, i, j, 0) == 0;
    } else {
        var val := if s[j - 1] == 0 then 1 else -1;
        calc {
            CalcBal(s, i, j, acc);
            == val + CalcBal(s, i, j - 1, acc);
            { CalcBalAppend(s, i, j - 1, acc); }
            == val + (acc + CalcBal(s, i, j - 1, 0));
            == acc + (val + CalcBal(s, i, j - 1, 0));
            == acc + CalcBal(s, i, j, 0);
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
    var bal1 := 0;
    var i := 0;
    while i < |s1|
        invariant 0 <= i <= |s1|
        invariant bal1 == CalcBal(s1, 0, i, 0)
        invariant forall k :: 0 <= k <= i ==> CalcBal(s1, 0, k, 0) >= 0
    {
        bal1 := bal1 + (if s1[i] == 0 then 1 else -1);
        i := i + 1;
        if bal1 < 0 {
            return false;
        }
    }
    
    var bal2 := bal1;
    i := 0;
    while i < |s2|
        invariant 0 <= i <= |s2|
        invariant bal2 == CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0)
        invariant forall k :: 0 <= k <= i ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, k, 0) >= 0
    {
        bal2 := bal2 + (if s2[i] == 0 then 1 else -1);
        i := i + 1;
        if bal2 < 0 {
            return false;
        }
    }
    
    return true;
}
// </vc-code>
