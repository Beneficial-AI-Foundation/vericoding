function CalcBal(s: seq<int>, i: int, j: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then 0
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1)
}

// <vc-helpers>
lemma CalcBalPrefix(s: seq<int>, i: int, j: int)
    requires 0 <= i <= j <= |s|
    ensures CalcBal(s, i, j) == CalcBal(s, 0, j) - CalcBal(s, 0, i)
{
    if i == j {
        assert CalcBal(s, i, j) == 0;
        assert CalcBal(s, 0, j) == CalcBal(s, 0, i);
    } else {
        CalcBalPrefix(s, i, j - 1);
        assert CalcBal(s, i, j) == (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1);
        assert CalcBal(s, 0, j) == (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, 0, j - 1);
        assert CalcBal(s, i, j) == CalcBal(s, 0, j) - CalcBal(s, 0, i);
    }
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
method correct_bracketing(s: seq<int>) returns (b: bool)
    // pre-conditions-start
    requires forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
    // pre-conditions-end
    // post-conditions-start
    ensures (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0) ==> b
    ensures b ==> (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0)
    // post-conditions-end
{
    var balance := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant balance == CalcBal(s, 0, i)
        invariant forall k :: 0 <= k <= i ==> CalcBal(s, 0, k) >= 0
    {
        if s[i] == 0 {
            balance := balance + 1;
        } else {
            balance := balance - 1;
        }
        if balance < 0 {
            return false;
        }
        i := i + 1;
    }
    return balance == 0;
}
// </vc-code>
