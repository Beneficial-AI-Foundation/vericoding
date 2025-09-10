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
function method ComputeMinAdditionalMatches(n: int): int
    requires n >= 2
    ensures ComputeMinAdditionalMatches(n) == MinAdditionalMatches(n)
{
    if n >= 4 then n % 2 else 4 - n
}
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<int>) returns (results: seq<int>)
    requires ValidInput(queries)
    ensures ValidResult(queries, results)
// </vc-spec>
// <vc-code>
{
    var results_arr: array<int> := new int[|queries|];
    var i: int := 0;
    while i < |queries|
        invariant 0 <= i <= |queries|
        invariant forall j :: 0 <= j < i ==> results_arr[j] == MinAdditionalMatches(queries[j])
    {
        results_arr[i] := ComputeMinAdditionalMatches(queries[i]);
        i := i + 1;
    }
    return results_arr.seq;
}
// </vc-code>

