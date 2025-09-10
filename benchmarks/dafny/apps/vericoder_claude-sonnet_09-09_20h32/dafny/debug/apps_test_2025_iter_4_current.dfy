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
lemma MaxCompositeSummandsProperties(n: int)
    requires n >= 1
    ensures MaxCompositeSummands(n) >= -1
{
    if n % 4 == 0 {
        assert n >= 4;  // Since n >= 1 and n % 4 == 0, smallest value is 4
        assert n / 4 >= 1;  // Therefore n / 4 >= 1 >= -1
    } else if n % 4 == 1 && n / 4 >= 2 {
        assert n / 4 - 1 >= 1;
    } else if n % 4 == 2 && n / 4 >= 1 {
        assert n / 4 >= 1;
    } else if n % 4 == 3 && n / 4 >= 3 {
        assert n / 4 - 1 >= 2;
    } else {
        assert MaxCompositeSummands(n) == -1;
    }
}

lemma ValidResultHelper(queries: seq<int>, results: seq<int>)
    requires ValidInput(queries)
    requires |results| == |queries|
    requires forall i :: 0 <= i < |queries| ==> results[i] == MaxCompositeSummands(queries[i])
    ensures ValidResult(queries, results)
{
    forall i | 0 <= i < |queries|
        ensures results[i] >= -1
    {
        MaxCompositeSummandsProperties(queries[i]);
    }
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
        invariant forall j :: 0 <= j < i ==> results[j] == MaxCompositeSummands(queries[j])
        invariant forall j :: 0 <= j < i ==> results[j] >= -1
    {
        var result := MaxCompositeSummands(queries[i]);
        MaxCompositeSummandsProperties(queries[i]);
        results := results + [result];
        i := i + 1;
    }
    ValidResultHelper(queries, results);
}
// </vc-code>

