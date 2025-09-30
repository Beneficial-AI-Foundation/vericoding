predicate ValidInput(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] == '+' || s[i] == '-'
}

function computeResult(s: string): int
    requires forall i :: 0 <= i < |s| ==> s[i] == '+' || s[i] == '-'
{
    computeResultHelper(s, 0, 0, 0, |s|)
}

function computeResultHelper(s: string, i: int, cur: int, pm: int, ans: int): int
    requires forall j :: 0 <= j < |s| ==> s[j] == '+' || s[j] == '-'
    requires 0 <= i <= |s|
    requires pm <= cur
    requires ans >= |s|
    decreases |s| - i
{
    if i == |s| then ans
    else if s[i] == '+' then
        computeResultHelper(s, i + 1, cur + 1, pm, ans)
    else
        var newCur := cur - 1;
        if newCur < pm then
            computeResultHelper(s, i + 1, newCur, newCur, ans + i + 1)
        else
            computeResultHelper(s, i + 1, newCur, pm, ans)
}

// <vc-helpers>
lemma ComputeResultEquivalence(s: string, i: int, cur: int, pm: int, ans: int)
    requires forall j :: 0 <= j < |s| ==> s[j] == '+' || s[j] == '-'
    requires 0 <= i <= |s|
    requires pm <= cur
    requires ans >= |s|
    ensures computeResultHelper(s, i, cur, pm, ans) >= |s|
    decreases |s| - i
{
    if i == |s| {
        // Base case: ans >= |s| by precondition
    } else if s[i] == '+' {
        ComputeResultEquivalence(s, i + 1, cur + 1, pm, ans);
    } else {
        var newCur := cur - 1;
        if newCur < pm {
            ComputeResultEquivalence(s, i + 1, newCur, newCur, ans + i + 1);
        } else {
            ComputeResultEquivalence(s, i + 1, newCur, pm, ans);
        }
    }
}

lemma ComputeResultStep(s: string, i: int, cur: int, pm: int, ans: int)
    requires forall j :: 0 <= j < |s| ==> s[j] == '+' || s[j] == '-'
    requires 0 <= i < |s|
    requires pm <= cur
    requires ans >= |s|
    ensures s[i] == '+' ==> computeResultHelper(s, i, cur, pm, ans) == computeResultHelper(s, i + 1, cur + 1, pm, ans)
    ensures s[i] == '-' && cur - 1 < pm ==> computeResultHelper(s, i, cur, pm, ans) == computeResultHelper(s, i + 1, cur - 1, cur - 1, ans + i + 1)
    ensures s[i] == '-' && cur - 1 >= pm ==> computeResultHelper(s, i, cur, pm, ans) == computeResultHelper(s, i + 1, cur - 1, pm, ans)
{
    // Follows directly from the definition of computeResultHelper
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result >= |s|
    ensures result == computeResult(s)
// </vc-spec>
// <vc-code>
{
    var i := 0;
    var cur := 0;
    var pm := 0;
    var ans := |s|;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant pm <= cur
        invariant ans >= |s|
        invariant computeResultHelper(s, 0, 0, 0, |s|) == computeResultHelper(s, i, cur, pm, ans)
    {
        if s[i] == '+' {
            cur := cur + 1;
        } else {
            cur := cur - 1;
            if cur < pm {
                pm := cur;
                ans := ans + i + 1;
            }
        }
        i := i + 1;
    }
    
    result := ans;
}
// </vc-code>

