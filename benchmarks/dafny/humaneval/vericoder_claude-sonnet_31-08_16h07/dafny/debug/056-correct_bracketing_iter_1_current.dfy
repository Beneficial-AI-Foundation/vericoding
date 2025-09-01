function CalcBal(s: seq<int>, i: int, j: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then 0
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1)
}

// <vc-helpers>
lemma CalcBalMonotonic(s: seq<int>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= |s|
    requires forall x :: 0 <= x < |s| ==> s[x] == 0 || s[x] == 1
    ensures CalcBal(s, i, k) == CalcBal(s, i, j) + CalcBal(s, j, k)
{
    if j == k {
        assert CalcBal(s, j, k) == 0;
    } else {
        CalcBalMonotonic(s, i, j, k - 1);
        assert CalcBal(s, i, k) == (if s[k - 1] == 0 then 1 else -1) + CalcBal(s, i, k - 1);
        assert CalcBal(s, i, k - 1) == CalcBal(s, i, j) + CalcBal(s, j, k - 1);
        assert CalcBal(s, j, k) == (if s[k - 1] == 0 then 1 else -1) + CalcBal(s, j, k - 1);
    }
}

lemma CalcBalStep(s: seq<int>, i: int)
    requires 0 <= i < |s|
    requires forall x :: 0 <= x < |s| ==> s[x] == 0 || s[x] == 1
    ensures CalcBal(s, 0, i + 1) == CalcBal(s, 0, i) + (if s[i] == 0 then 1 else -1)
{
    CalcBalMonotonic(s, 0, i, i + 1);
    assert CalcBal(s, i, i + 1) == (if s[i] == 0 then 1 else -1);
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
    b := true;
    var balance := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant balance == CalcBal(s, 0, i)
        invariant b ==> (forall j :: 0 <= j <= i ==> CalcBal(s, 0, j) >= 0)
    {
        if s[i] == 0 {
            balance := balance + 1;
        } else {
            balance := balance - 1;
        }
        
        CalcBalStep(s, i);
        i := i + 1;
        
        if balance < 0 {
            b := false;
        }
    }
}
// </vc-code>

