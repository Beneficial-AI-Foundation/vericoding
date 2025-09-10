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
lemma Helper_ge_ans(s: string, i: int, cur: int, pm: int, ans: int)
    requires forall j :: 0 <= j < |s| ==> s[j] == '+' || s[j] == '-'
    requires 0 <= i <= |s|
    requires pm <= cur
    requires ans >= |s|
    ensures computeResultHelper(s, i, cur, pm, ans) >= ans
    decreases |s| - i
{
    if i == |s| {
        // computeResultHelper(s,|s|,...)=ans
        assert computeResultHelper(s, i, cur, pm, ans) == ans;
    } else if s[i] == '+' {
        Helper_ge_ans(s, i + 1, cur + 1, pm, ans);
        // by function-body: computeResultHelper(s,i,cur,pm,ans) == computeResultHelper(s,i+1,cur+1,pm,ans)
        assert computeResultHelper(s, i, cur, pm, ans) == computeResultHelper(s, i + 1, cur + 1, pm, ans);
    } else {
        var newCur := cur - 1;
        if newCur < pm {
            Helper_ge_ans(s, i + 1, newCur, newCur, ans + i + 1);
            // by function-body: computeResultHelper(s,i,cur,pm,ans) == computeResultHelper(s,i+1,newCur,newCur,ans+i+1)
            assert computeResultHelper(s, i, cur, pm, ans) == computeResultHelper(s, i + 1, newCur, newCur, ans + i + 1);
        } else {
            Helper_ge_ans(s, i + 1, newCur, pm, ans);
            // by function-body: computeResultHelper(s,i,cur,pm,ans) == computeResultHelper(s,i+1,newCur,pm,ans)
            assert computeResultHelper(s, i, cur, pm, ans) == computeResultHelper(s, i + 1, newCur, pm, ans);
        }
    }
    // In all branches, the recursive call (or base case) established the bound
    assert computeResultHelper(s, i, cur, pm, ans) >= ans;
}

lemma computeResult_ge_length(s: string)
    requires ValidInput(s)
    ensures computeResult(s) >= |s|
{
    // computeResult(s) == computeResultHelper(s,0,0,0,|s|)
    Helper_ge_ans(s, 0, 0, 0, |s|);
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
  result := computeResult(s);
  computeResult_ge_length(s);
}
// </vc-code>

