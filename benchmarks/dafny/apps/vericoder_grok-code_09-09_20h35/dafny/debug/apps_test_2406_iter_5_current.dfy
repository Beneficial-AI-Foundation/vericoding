predicate ValidInput(n: int, heights: seq<int>)
{
    n > 0 && |heights| == n &&
    (forall i :: 0 <= i < n ==> heights[i] >= 0) &&
    (forall i :: 0 <= i < n-1 ==> heights[i] < heights[i+1])
}

predicate ValidOutput(n: int, result: seq<int>)
{
    |result| == n &&
    (forall i :: 0 <= i < n ==> result[i] >= 0) &&
    (forall i :: 0 <= i < n-1 ==> result[i] <= result[i+1]) &&
    (forall i :: 0 <= i < n-1 ==> result[i+1] - result[i] <= 1)
}

predicate IsStable(result: seq<int>)
{
    forall i :: 0 <= i < |result|-1 ==> !(result[i] + 2 <= result[i+1])
}

function sum_seq(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum_seq(s[1..])
}

// <vc-helpers>
lemma SumLemma(n: int, q: int, r: int, heights: seq<int>, S: int)
requires ValidInput(n, heights)
requires S == sum_seq(heights)
requires q == S / n && r == S % n
ensures (n - r)*q + r*(q+1) == S
{}
// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, heights)
    ensures ValidOutput(n, result)
    ensures sum_seq(result) == sum_seq(heights)
    ensures IsStable(result)
// </vc-spec>
// <vc-code>
{
    var S := 0;
    for i := 0 to n - 1
      invariant 0 <= i <= n
      invariant S == sum_seq(heights[..i])
    {
        S := S + heights[i];
    }
    var q := S / n;
    var r := S % n;
    SumLemma(n, q, r, heights, S);
    var res := [];
    var res_sum := 0;
    for i := 0 to n-1
      invariant 0 <= i <= n
      invariant |res| == i
      invariant res_sum == sum_seq(res)
      invariant forall j::0<=j<i :: (j < n - r ==> res[j] == q) && (j >= n - r ==> res[j] == q+1)
    {
        if i < n - r {
            res := res + [q];
            res_sum := res_sum + q;
        } else {
            res := res + [q+1];
            res_sum := res_sum + q + 1;
        }
    }
    assert res_sum == S;
    result := res;
}
// </vc-code>

