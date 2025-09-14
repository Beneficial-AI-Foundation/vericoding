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
method ComputeMaxCompositeSummands(n: int) returns (res: int)
    ensures res == MaxCompositeSummands(n)
{
    if n % 4 == 0 {
        res := n / 4;
    } else if n % 4 == 1 && n / 4 >= 2 {
        res := n / 4 - 1;
    } else if n % 4 == 2 && n / 4 >= 1 {
        res := n / 4;
    } else if n % 4 == 3 && n / 4 >= 3 {
        res := n / 4 - 1;
    } else {
        res := -1;
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
    var arr := new int[|queries|];
    for i := 0 to |queries|
        invariant 0 <= i <= |queries|
        invariant forall j :: 0 <= j < i ==> arr[j] == MaxCompositeSummands(queries[j])
    {
        arr[i] := ComputeMaxCompositeSummands(queries[i]);
    }
    return arr[..];
}
// </vc-code>

