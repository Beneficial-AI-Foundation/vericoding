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
lemma MinAdditionalMatchesCorrect(n: int)
    requires n >= 2
    ensures MinAdditionalMatches(n) == (if n >= 4 then n % 2 else 4 - n)
{
}

lemma ValidResultProperty(queries: seq<int>, results: seq<int>, i: int)
    requires ValidInput(queries)
    requires 0 <= i < |queries|
    requires |results| == |queries|
    requires results[i] == MinAdditionalMatches(queries[i])
    ensures results[i] == MinAdditionalMatches(queries[i])
{
}
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
        invariant 0 <= i <= |queries|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> results[j] == MinAdditionalMatches(queries[j])
    {
        var additional := MinAdditionalMatches(queries[i]);
        results := results + [additional];
        i := i + 1;
    }
}
// </vc-code>

