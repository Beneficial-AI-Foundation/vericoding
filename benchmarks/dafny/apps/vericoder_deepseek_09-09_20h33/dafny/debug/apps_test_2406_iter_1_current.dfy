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
lemma MonotonicSum(s: seq<int>)
  requires forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
  ensures forall i,j :: 0 <= i <= j < |s| ==> s[i] <= s[j]
{
}

lemma GapLemma(s: seq<int>)
  requires |s| > 0
  requires forall i :: 0 <= i < |s|-1 ==> s[i+1] - s[i] <= 1
  ensures forall i,j :: 0 <= i <= j < |s| ==> s[j] - s[i] <= j - i
{
}

lemma StabilityLemma(s: seq<int>)
  requires IsStable(s)
  ensures forall i,j :: 0 <= i < j < |s| ==> s[j] - s[i] <= j - i
{
}
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
    result := heights;
    
    var changed: bool := true;
    while changed
        invariant ValidOutput(n, result)
        invariant sum_seq(result) == sum_seq(heights)
        invariant IsStable(result)
        decreases sum_seq(result) + n
    {
        changed := false;
        var i := 0;
        while i < n-1
            invariant 0 <= i <= n-1
            invariant ValidOutput(n, result)
            invariant sum_seq(result) == sum_seq(heights)
            invariant IsStable(result)
            decreases n - i
        {
            if result[i] + 2 <= result[i+1] {
                result := result[i := result[i] + 1];
                result := result[i+1 := result[i+1] - 1];
                changed := true;
            } else {
                i := i + 1;
            }
        }
    }
}
// </vc-code>

