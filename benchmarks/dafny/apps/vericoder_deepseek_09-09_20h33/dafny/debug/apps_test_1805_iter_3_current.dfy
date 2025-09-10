predicate ValidInput(queries: seq<int>) {
    forall i :: 0 <= i < |queries| ==> queries[i] >= 2
}

function MinAdditionalMatches(n: int): int
    requires n >= 2
{
    if n >= 4 then n % 2 else 4 - n
}

predicate ValidResult(queries: seq<int>, results: seq<int>)
    requires ValidInput(queries)
{
    |results| == |queries| &&
    forall i :: 0 <= i < |queries| ==> results[i] == MinAdditionalMatches(queries[i])
}

// <vc-helpers>
lemma MinAdditionalMatchesLemma(n: int)
    requires n >= 2
    ensures MinAdditionalMatches(n) == (if n >= 4 then n % 2 else 4 - n)
{
}

lemma MinAdditionalMatchesProperties(n: int)
    requires n >= 2
    ensures 0 <= MinAdditionalMatches(n) <= 2
{
    MinAdditionalMatchesLemma(n);
    if n >= 4 {
        assert n % 2 == 0 || n % 2 == 1;
    } else {
        assert n == 2 || n == 3;
        if n == 2 { assert 4 - n == 2; }
        if n == 3 { assert 4 - n == 1; }
    }
}

lemma ValidInputLemma(queries: seq<int>, j: int)
    requires ValidInput(queries)
    requires 0 <= j < |queries|
    ensures queries[j] >= 2
{
}

lemma ValidInputSliceLemma(queries: seq<int>, i: int)
    requires ValidInput(queries)
    requires 0 <= i <= |queries|
    ensures ValidInput(queries[0..i])
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<int>) returns (results: seq<int>)
    requires ValidInput(queries)
    ensures ValidResult(queries, results)
// </vc-spec>
// <vc-code>
{
    results := [];
    var i := 0;
    while i < |queries|
        invariant |results| == i
        invariant ValidInput(queries[0..i])
        invariant forall j :: 0 <= j < i ==> results[j] == MinAdditionalMatches(queries[j])
    {
        ValidInputSliceLemma(queries, i);
        ValidInputLemma(queries, i);
        var n := queries[i];
        MinAdditionalMatchesProperties(n);
        var result := if n >= 4 then n % 2 else 4 - n;
        results := results + [result];
        i := i + 1;
    }
}
// </vc-code>

