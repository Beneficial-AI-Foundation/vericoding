function CalcBal(s: seq<int>, i: int, j: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then 0
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1)
}

// <vc-helpers>
lemma CalcBalAdditive(s: seq<int>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= |s|
    ensures CalcBal(s, i, k) == CalcBal(s, i, j) + CalcBal(s, j, k)
{
    if j == k {
        assert CalcBal(s, j, k) == 0;
    } else {
        CalcBalAdditive(s, i, j, k - 1);
    }
}

lemma CalcBalMonotonic(s: seq<int>, i: int, j: int)
    requires 0 <= i <= j <= |s|
    requires forall k :: i <= k < j ==> s[k] == 0 || s[k] == 1
    requires forall k :: i <= k <= j ==> CalcBal(s, i, k) >= 0
    ensures CalcBal(s, i, j) >= 0
{
    if i < j {
        assert CalcBal(s, i, j) >= 0;
    }
}

lemma NegativeBalanceImpliesNotAllPositive(s: seq<int>, idx: int)
    requires 0 <= idx < |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
    requires forall i :: 0 <= i <= idx ==> CalcBal(s, 0, i) >= 0
    requires CalcBal(s, 0, idx + 1) < 0
    ensures !(forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0)
{
    assert CalcBal(s, 0, idx + 1) < 0;
    assert !(CalcBal(s, 0, idx + 1) >= 0);
}
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
    var idx := 0;
    
    while idx < |s|
        invariant 0 <= idx <= |s|
        invariant balance == CalcBal(s, 0, idx)
        invariant forall i :: 0 <= i <= idx ==> CalcBal(s, 0, i) >= 0
    {
        if s[idx] == 0 {
            balance := balance + 1;
        } else {
            balance := balance - 1;
        }
        
        idx := idx + 1;
        assert CalcBal(s, 0, idx) == balance;
        
        if balance < 0 {
            NegativeBalanceImpliesNotAllPositive(s, idx - 1);
            b := false;
            return;
        }
    }
    
    assert idx == |s|;
    assert balance == CalcBal(s, 0, |s|);
    assert forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0;
    
    b := (balance == 0);
}
// </vc-code>

