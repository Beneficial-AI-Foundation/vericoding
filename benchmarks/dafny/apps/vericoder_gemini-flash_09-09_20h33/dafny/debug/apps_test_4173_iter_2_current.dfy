predicate ValidQuery(query: (int, int, int))
{
    query.0 > 0 && query.1 > 0 && query.2 > 0
}

function MinCostForQuery(n: int, a: int, b: int): int
    requires n > 0 && a > 0 && b > 0
{
    if n % 2 == 0 then
        if n * a <= (n / 2) * b then n * a else (n / 2) * b
    else
        if n * a <= (n / 2) * b + a then n * a else (n / 2) * b + a
}

// <vc-helpers>
function MinCostForQueryWrapper(query: (int, int, int)): int
    requires ValidQuery(query)
{
    var n := query.0;
    var a := query.1;
    var b := query.2;
    if n % 2 == 0 then
        if n * a <= (n / 2) * b then n * a else (n / 2) * b
    else
        if n * a <= (n / 2) * b + a then n * a else (n / 2) * b + a
}
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<(int, int, int)>) returns (results: seq<int>)
    requires forall i | 0 <= i < |queries| :: ValidQuery(queries[i])
    ensures |results| == |queries|
    ensures forall i | 0 <= i < |queries| :: 
        var n := queries[i].0;
        var a := queries[i].1;
        var b := queries[i].2;
        results[i] == (if n % 2 == 0 then
            if n * a <= (n / 2) * b then n * a else (n / 2) * b
        else
            if n * a <= (n / 2) * b + a then n * a else (n / 2) * b + a)
// </vc-spec>
// <vc-code>
{
    var results_arr: array<int>;
    if |queries| > 0 {
        results_arr := new int[|queries|];
        for i := 0 to |queries| - 1
            invariant 0 <= i <= |queries|
            invariant forall j | 0 <= j < i ::
                results_arr[j] == MinCostForQueryWrapper(queries[j])
        {
            results_arr[i] := MinCostForQueryWrapper(queries[i]);
        }
        results := results_arr[..];
    } else {
        results := [];
    }
}
// </vc-code>

