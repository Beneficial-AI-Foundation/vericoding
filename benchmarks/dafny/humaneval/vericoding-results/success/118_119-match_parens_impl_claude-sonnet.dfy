// <vc-preamble>
function CalcBal(s: seq<int>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1, acc)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed invalid functions with while loops, kept only valid lemma */
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

function ComputeBalance(s: seq<int>, i: int): int
    requires 0 <= i <= |s|
    requires forall j :: 0 <= j < |s| ==> s[j] == 0 || s[j] == 1
{
    CalcBal(s, 0, i, 0)
}
// </vc-helpers>

// <vc-spec>
method checkFixed(s1: seq<int>, s2: seq<int>) returns (b: bool) 

    requires forall i :: 0 <= i < |s1| ==> s1[i] == 0 || s1[i] == 1
    requires forall i :: 0 <= i < |s2| ==> s2[i] == 0 || s2[i] == 1

    ensures b ==> forall i :: 0 <= i <= |s1| ==> CalcBal(s1, 0, i, 0) >= 0
    ensures b ==> forall i :: 0 <= i <= |s2| ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) >= 0
    ensures !b ==> (exists i :: 0 <= i <= |s1| && CalcBal(s1, 0, i, 0) < 0) || (exists i :: 0 <= i <= |s2| && CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) < 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed while loop syntax and implementation */
    var i := 0;
    while i <= |s1|
        invariant 0 <= i <= |s1| + 1
        invariant forall k :: 0 <= k < i ==> CalcBal(s1, 0, k, 0) >= 0
    {
        if CalcBal(s1, 0, i, 0) < 0 {
            b := false;
            assert CalcBal(s1, 0, i, 0) < 0;
            assert exists j :: 0 <= j <= |s1| && CalcBal(s1, 0, j, 0) < 0;
            return;
        }
        i := i + 1;
    }
    
    var s1_total := CalcBal(s1, 0, |s1|, 0);
    i := 0;
    while i <= |s2|
        invariant 0 <= i <= |s2| + 1
        invariant forall k :: 0 <= k < i ==> s1_total + CalcBal(s2, 0, k, 0) >= 0
        invariant forall k :: 0 <= k <= |s1| ==> CalcBal(s1, 0, k, 0) >= 0
    {
        if s1_total + CalcBal(s2, 0, i, 0) < 0 {
            b := false;
            assert s1_total + CalcBal(s2, 0, i, 0) < 0;
            assert exists j :: 0 <= j <= |s2| && CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, j, 0) < 0;
            return;
        }
        i := i + 1;
    }
    
    b := true;
}
// </vc-code>
