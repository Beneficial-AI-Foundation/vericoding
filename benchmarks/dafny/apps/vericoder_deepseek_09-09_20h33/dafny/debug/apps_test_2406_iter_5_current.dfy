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

lemma SumPreservationLemma(s: seq<int>, i: int, old_val1: int, new_val1: int, old_val2: int, new_val2: int)
  requires 0 <= i < |s| - 1
  requires new_val1 == old_val1 + 1 && new_val2 == old_val2 - 1
  ensures sum_seq(s[i := new_val1][i+1 := new_val2]) == sum_seq(s)
{
  calc {
    sum_seq(s[i := new_val1][i+1 := new_val2]);
    == {
      assert s[i := new_val1][i+1 := new_val2] == s[0..i] + [new_val1] + [new_val2] + s[i+2..];
    }
    sum_seq(s[0..i]) + new_val1 + new_val2 + sum_seq(s[i+2..]);
    == { assert old_val1 == s[i]; assert old_val2 == s[i+1]; }
    sum_seq(s[0..i]) + (old_val1 + 1) + (old_val2 - 1) + sum_seq(s[i+2..]);
    ==
    sum_seq(s[0..i]) + old_val1 + old_val2 + sum_seq(s[i+2..]);
    ==
    sum_seq(s);
  }
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
        invariant |result| == n
        invariant forall i :: 0 <= i < n ==> result[i] >= 0
        invariant sum_seq(result) == sum_seq(heights)
        invariant forall j,k :: 0 <= j < k < n ==> result[k] - result[j] >= 0
        invariant IsStable(result)
        decreases *(1024)
    {
        changed := false;
        var i := 0;
        while i < n-1
            invariant 0 <= i <= n-1
            invariant |result| == n
            invariant forall j :: 0 <= j < n ==> result[j] >= 0
            invariant sum_seq(result) == sum_seq(heights)
            invariant forall j,k :: 0 <= j < k < n ==> result[k] - result[j] >= 0
            invariant IsStable(result)
            decreases n - i
        {
            if result[i] + 2 <= result[i+1] {
                var old_i := result[i];
                var old_i1 := result[i+1];
                result := result[i := old_i + 1];
                result := result[i+1 := old_i1 - 1];
                changed := true;
                i := 0;
            } else {
                i := i + 1;
            }
        }
    }
}
// </vc-code>

