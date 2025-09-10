predicate IsComposite(x: int)
{
    x >= 4 && exists k :: 2 <= k < x && x % k == 0
}

predicate ValidInput(queries: seq<int>)
{
    forall i :: 0 <= i < |queries| ==> queries[i] >= 1
}

function MaxCompositeSummands(n: int): int
{
    if n % 4 == 0 then n / 4
    else if n % 4 == 1 && n / 4 >= 2 then n / 4 - 1
    else if n % 4 == 2 && n / 4 >= 1 then n / 4
    else if n % 4 == 3 && n / 4 >= 3 then n / 4 - 1
    else -1
}

predicate ValidResult(queries: seq<int>, results: seq<int>)
{
    |results| == |queries| &&
    forall i :: 0 <= i < |queries| ==> results[i] == MaxCompositeSummands(queries[i]) &&
    forall i :: 0 <= i < |queries| ==> results[i] >= -1
}

// <vc-helpers>
function MaxCompositeSummandsMethod(n: int): int
{
    if n % 4 == 0 then n / 4
    else if n % 4 == 1 then
        if n / 4 >= 2 then n / 4 - 1
        else -1
    else if n % 4 == 2 then
        if n / 4 >= 1 then n / 4
        else -1
    else if n % 4 == 3 then
        if n / 4 >= 3 then n / 4 - 1
        else -1
    else -1 // Should not be reached for n >= 1
}
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<int>) returns (results: seq<int>)
    requires ValidInput(queries)
    ensures ValidResult(queries, results)
// </vc-spec>
// <vc-code>
{
    var results_seq: seq<int> := new int[|queries|]((_ : int) => 0);
    var i := 0;
    while i < |queries|
        invariant 0 <= i <= |queries|
        invariant |results_seq| == |queries|
        invariant forall k :: 0 <= k < i ==> results_seq[k] == MaxCompositeSummands(queries[k])
        invariant forall k :: 0 <= k < i ==> results_seq[k] >= -1
    {
        var n := queries[i];
        var result_n := MaxCompositeSummandsMethod(n);

        results_seq := results_seq[i := result_n];
        i := i + 1;
    }
    return results_seq;
}
// </vc-code>

