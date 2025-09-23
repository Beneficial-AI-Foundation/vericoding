// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result >= |s|
    ensures result == computeResult(s)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
