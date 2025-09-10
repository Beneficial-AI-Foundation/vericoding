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
// </vc-helpers>
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
    for i := 0 to n - 1 {
        S := S + heights[i];
    }
    var q := S / n;
    var r := S % n;
    var result := [];
    for i := 0 to n-1 {
        if i < n - r {
            result := result + [q];
        } else {
            result := result + [q + 1];
        }
    }
}
// </vc-code>

