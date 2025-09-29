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
lemma RangeSumProperty(l: int, r: int)
    requires l >= 1
    ensures RangeSum(l, r) == if l > r then 0 else PrefixSum(r) - PrefixSum(l - 1)
    decreases r - l + 1
{
    if l > r {
        assert RangeSum(l, r) == 0;
    } else if l == r {
        // Base case: single element
        assert RangeSum(l, r) == ArrayElement(l);
        SingleElementSum(l);
    } else {
        // Recursive case
        assert RangeSum(l, r) == ArrayElement(l) + RangeSum(l + 1, r);
        RangeSumProperty(l + 1, r);
        assert RangeSum(l + 1, r) == PrefixSum(r) - PrefixSum(l);
        SingleElementSum(l);
        assert ArrayElement(l) == PrefixSum(l) - PrefixSum(l - 1);
        assert RangeSum(l, r) == (PrefixSum(l) - PrefixSum(l - 1)) + (PrefixSum(r) - PrefixSum(l));
        assert RangeSum(l, r) == PrefixSum(r) - PrefixSum(l - 1);
    }
}

lemma SingleElementSum(k: int)
    requires k >= 1
    ensures ArrayElement(k) == PrefixSum(k) - PrefixSum(k - 1)
{
    if k % 2 == 1 {
        // k is odd
        assert ArrayElement(k) == -k;
        assert PrefixSum(k) == -(k + 1) / 2;
        assert PrefixSum(k - 1) == (k - 1) / 2;
        assert PrefixSum(k) - PrefixSum(k - 1) == -(k + 1) / 2 - (k - 1) / 2;
        assert PrefixSum(k) - PrefixSum(k - 1) == (-(k + 1) - (k - 1)) / 2;
        assert PrefixSum(k) - PrefixSum(k - 1) == -2 * k / 2;
        assert PrefixSum(k) - PrefixSum(k - 1) == -k;
    } else {
        // k is even
        assert ArrayElement(k) == k;
        assert PrefixSum(k) == k / 2;
        assert PrefixSum(k - 1) == -k / 2;
        assert PrefixSum(k) - PrefixSum(k - 1) == k / 2 - (-k / 2);
        assert PrefixSum(k) - PrefixSum(k - 1) == k / 2 + k / 2;
        assert PrefixSum(k) - PrefixSum(k - 1) == k;
    }
}

lemma ValidQueryImpliesNoEmpty(l: int, r: int)
    requires l >= 1 && l <= r
    ensures RangeSum(l, r) == PrefixSum(r) - PrefixSum(l - 1)
{
    RangeSumProperty(l, r);
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
    for i := 0 to |queries|
        invariant 0 <= i <= |queries|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> results[j] == PrefixSum(queries[j].1) - PrefixSum(queries[j].0 - 1)
    {
        var l := queries[i].0;
        var r := queries[i].1;
        var sum := PrefixSum(r) - PrefixSum(l - 1);
        results := results + [sum];
        
        // Verify that our computation matches RangeSum
        assert ValidQuery(queries[i]);
        assert l >= 1 && l <= r;
        ValidQueryImpliesNoEmpty(l, r);
    }
}
// </vc-code>

