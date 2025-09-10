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
lemma RangeSumFormula(l: int, r: int)
    requires l >= 1
    ensures RangeSum(l, r) == PrefixSum(r) - PrefixSum(l - 1)
    decreases r - l + 1
{
    if l > r {
        assert RangeSum(l, r) == 0;
        PrefixSumBaseCaseProperty(l - 1, r);
    } else {
        assert RangeSum(l, r) == ArrayElement(l) + RangeSum(l + 1, r);
        RangeSumFormula(l + 1, r);
        assert RangeSum(l + 1, r) == PrefixSum(r) - PrefixSum(l);
        assert RangeSum(l, r) == ArrayElement(l) + PrefixSum(r) - PrefixSum(l);
        PrefixSumStepProperty(l - 1, l);
        assert PrefixSum(l) - PrefixSum(l - 1) == ArrayElement(l);
        assert RangeSum(l, r) == PrefixSum(r) - PrefixSum(l - 1);
    }
}

lemma PrefixSumBaseCaseProperty(k1: int, k2: int)
    requires k1 >= k2
    ensures PrefixSum(k2) - PrefixSum(k1) == RangeSum(k1 + 1, k2)
{
    assert RangeSum(k1 + 1, k2) == 0;
}

lemma PrefixSumStepProperty(k1: int, k2: int)
    requires k1 + 1 == k2
    ensures PrefixSum(k2) - PrefixSum(k1) == ArrayElement(k2)
{
    assert RangeSum(k2, k2) == ArrayElement(k2);
}

lemma PrefixSumProperty(k1: int, k2: int)
    requires k1 < k2
    ensures PrefixSum(k2) - PrefixSum(k1) == RangeSum(k1 + 1, k2)
    decreases k2 - k1
{
    if k1 + 1 > k2 {
        assert RangeSum(k1 + 1, k2) == 0;
    } else {
        RangeSumFormula(k1 + 1, k2);
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
        invariant 0 <= i <= |queries|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> results[j] == PrefixSum(queries[j].1) - PrefixSum(queries[j].0 - 1)
    {
        var query := queries[i];
        var l := query.0;
        var r := query.1;
        
        RangeSumFormula(l, r);
        var result := PrefixSum(r) - PrefixSum(l - 1);
        results := results + [result];
        i := i + 1;
    }
}
// </vc-code>

