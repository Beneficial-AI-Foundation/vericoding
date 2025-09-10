predicate ValidInput(n: int, k: int)
{
    n > 0 && k > 0
}

predicate IsStrictlyIncreasing(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i+1]
}

predicate AllPositive(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] > 0
}

function sum(s: seq<int>): int
    decreases |s|
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidSequence(s: seq<int>, n: int, k: int)
{
    |s| == k && AllPositive(s) && IsStrictlyIncreasing(s) && sum(s) == n
}

predicate IsPossible(n: int, k: int)
{
    k * (k + 1) / 2 <= n
}

// <vc-helpers>
lemma AllPositiveConcat(s1: seq<int>, s2: seq<int>)
    requires AllPositive(s1) && AllPositive(s2)
    ensures AllPositive(s1 + s2)
{
}

lemma IsStrictlyIncreasingConcat(s1: seq<int>, s2: seq<int>)
    requires IsStrictlyIncreasing(s1) && IsStrictlyIncreasing(s2) && (|s1| == 0 || |s2| == 0 || s1[|s1|-1] < s2[0])
    ensures IsStrictlyIncreasing(s1 + s2)
{
}

lemma SumConcat(s1: seq<int>, s2: seq<int>)
    ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
}

lemma MinimumSum(k: int) returns (s: seq<int>)
    requires k > 0
    ensures |s| == k && IsStrictlyIncreasing(s) && AllPositive(s) && sum(s) == k*(k+1)/2
    ensures forall t :: |t| == k && IsStrictlyIncreasing(t) && AllPositive(t) ==> sum(t) >= k*(k+1)/2
{
    s := [];
    var i := 1;
    while i <= k
        invariant |s| == i-1
        invariant IsStrictlyIncreasing(s)
        invariant AllPositive(s)
        invariant sum(s) == (i-1)*i/2
        invariant forall j :: 0 <= j < |s| ==> s[j] == j+1
    {
        s := s + [i];
        i := i + 1;
    }
}

lemma IsPossibleImpliesSolutionExists(n: int, k: int)
    requires ValidInput(n, k)
    requires IsPossible(n, k)
    ensures exists result :: ValidSequence(result, n, k)
{
    var min_seq := MinimumSum(k);
    var remaining := n - sum(min_seq);
    
    if remaining > 0 {
        var result := min_seq;
        var i := k - 1;
        while remaining > 0 && i >= 0
            invariant 0 <= i <= k-1
            invariant |result| == k
            invariant IsStrictlyIncreasing(result)
            invariant AllPositive(result)
            invariant sum(result) == n - remaining
        {
            result := result[0..i] + [result[i] + 1] + result[i+1..];
            remaining := remaining - 1;
            i := if i > 0 then i - 1 else k - 1;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures (|result| == 1 && result[0] == -1) || 
            (ValidSequence(result, n, k))
    ensures (|result| == 1 && result[0] == -1) <==> !IsPossible(n, k)
// </vc-spec>
// <vc-code>
{
    if !IsPossible(n, k) {
        result := [-1];
    } else {
        var min_seq := MinimumSum(k);
        var remaining := n - sum(min_seq);
        result := min_seq;
        var i := k - 1;
        
        while remaining > 0
            invariant |result| == k
            invariant IsStrictlyIncreasing(result)
            invariant AllPositive(result)
            invariant sum(result) == n - remaining
        {
            result := result[0..i] + [result[i] + 1] + result[i+1..];
            remaining := remaining - 1;
            i := if i > 0 then i - 1 else k - 1;
        }
    }
}
// </vc-code>

