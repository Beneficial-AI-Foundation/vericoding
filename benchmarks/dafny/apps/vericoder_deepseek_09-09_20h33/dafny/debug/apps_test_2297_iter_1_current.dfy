predicate ValidQuery(query: (int, int))
{
    query.0 >= 1 && query.0 <= query.1
}

predicate ValidInput(queries: seq<(int, int)>)
{
    forall i :: 0 <= i < |queries| ==> ValidQuery(queries[i])
}

function ArrayElement(i: int): int
    requires i >= 1
{
    i * (if i % 2 == 1 then -1 else 1)
}

function RangeSum(l: int, r: int): int
    requires l >= 1
    decreases r - l + 1
{
    if l > r then 0 else ArrayElement(l) + RangeSum(l + 1, r)
}

function PrefixSum(k: int): int
{
    if k % 2 == 0 then k / 2 else -(k + 1) / 2
}

predicate CorrectResult(queries: seq<(int, int)>, results: seq<int>)
    requires ValidInput(queries)
{
    |results| == |queries| &&
    forall i :: 0 <= i < |queries| ==> results[i] == PrefixSum(queries[i].1) - PrefixSum(queries[i].0 - 1)
}

// <vc-helpers>
lemma PrefixSumCorrectness(l: int, r: int)
    requires l >= 1
    ensures RangeSum(l, r) == PrefixSum(r) - PrefixSum(l - 1)
{
    // The proof follows from mathematical induction on the relationship
    // between ArrayElement and PrefixSum functions
    if r < l {
        assert RangeSum(l, r) == 0;
        assert PrefixSum(r) - PrefixSum(l - 1) == 0;
    } else {
        // Recursively prove for smaller ranges
        PrefixSumCorrectness(l, r - 1);
        // The current element contributes to the sum
        assert RangeSum(l, r) == RangeSum(l, r - 1) + ArrayElement(r);
        // Show the relationship with PrefixSum
        assert PrefixSum(r) - PrefixSum(l - 1) == (PrefixSum(r - 1) - PrefixSum(l - 1)) + ArrayElement(r);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<(int, int)>) returns (results: seq<int>)
    requires ValidInput(queries)
    ensures CorrectResult(queries, results)
// </vc-spec>
// <vc-code>
{
    results := [];
    var i := 0;
    while i < |queries|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> results[j] == PrefixSum(queries[j].1) - PrefixSum(queries[j].0 - 1)
    {
        var l, r := queries[i].0, queries[i].1;
        // Calculate result using PrefixSum formula
        var res := PrefixSum(r) - PrefixSum(l - 1);
        results := results + [res];
        i := i + 1;
    }
}
// </vc-code>

