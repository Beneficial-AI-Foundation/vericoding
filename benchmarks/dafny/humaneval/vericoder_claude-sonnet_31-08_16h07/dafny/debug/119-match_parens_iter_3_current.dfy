function CalcBal(s: seq<int>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1, acc)
}

// <vc-helpers>
lemma CalcBalMonotonic(s: seq<int>, i: int, j: int, k: int, acc: int)
    requires 0 <= i <= j <= k <= |s|
    requires forall x :: 0 <= x < |s| ==> s[x] == 0 || s[x] == 1
    ensures CalcBal(s, i, k, acc) == CalcBal(s, j, k, CalcBal(s, i, j, acc))
{
    if j == k {
    } else {
        CalcBalMonotonic(s, i, j, k-1, acc);
    }
}

lemma CalcBalAdditive(s: seq<int>, i: int, j: int, acc1: int, acc2: int)
    requires 0 <= i <= j <= |s|
    requires forall x :: 0 <= x < |s| ==> s[x] == 0 || s[x] == 1
    ensures CalcBal(s, i, j, acc1 + acc2) == CalcBal(s, i, j, acc1) + acc2
{
    if i == j {
    } else {
        CalcBalAdditive(s, i, j-1, acc1, acc2);
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
    var s1_bal := 0;
    var i := 0;
    
    while i < |s1|
        invariant 0 <= i <= |s1|
        invariant s1_bal == CalcBal(s1, 0, i, 0)
        invariant forall k :: 0 <= k <= i ==> CalcBal(s1, 0, k, 0) >= 0
    {
        s1_bal := s1_bal + (if s1[i] == 0 then 1 else -1);
        i := i + 1;
        if s1_bal < 0 {
            return false;
        }
    }
    
    var s2_bal := s1_bal;
    var j := 0;
    
    while j < |s2|
        invariant 0 <= j <= |s2|
        invariant s2_bal == s1_bal + CalcBal(s2, 0, j, 0)
        invariant forall k :: 0 <= k <= j ==> s1_bal + CalcBal(s2, 0, k, 0) >= 0
    {
        s2_bal := s2_bal + (if s2[j] == 0 then 1 else -1);
        j := j + 1;
        if s2_bal < 0 {
            return false;
        }
    }
    
    return true;
}
// </vc-code>

