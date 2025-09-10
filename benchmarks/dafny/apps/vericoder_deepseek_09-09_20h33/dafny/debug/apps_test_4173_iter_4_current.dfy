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
lemma MinCostForQueryCorrect(n: int, a: int, b: int)
    requires n > 0 && a > 0 && b > 0
    ensures MinCostForQuery(n, a, b) == (if n % 2 == 0 then
            if n * a <= (n / 2) * b then n * a else (n / 2) * b
        else
            if n * a <= (n / 2) * b + a then n * a else (n / 2) * b + a)
{
}

lemma IndexInRange(s: seq<(int, int, int)>, j: int)
    requires 0 <= j < |s|
    ensures j < |s|
{
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
    results := [];
    var i := 0;
    while i < |queries|
        invariant |results| == i
        invariant forall j | 0 <= j < i :: 
            var n := queries[j].0;
            var a := queries[j].1;
            var b := queries[j].2;
            results[j] == MinCostForQuery(n, a, b)
    {
        var query := queries[i];
        var n := query.0;
        var a := query.1;
        var b := query.2;
        assert n > 0 && a > 0 && b > 0;
        MinCostForQueryCorrect(n, a, b);
        results := results + [MinCostForQuery(n, a, b)];
        i := i + 1;
        
        // Prove the invariant for all j < i
        var j: int := 0;
        while j < i
            invariant forall k | 0 <= k < j :: 
                var n := queries[k].0;
                var a := queries[k].1;
                var b := queries[k].2;
                results[k] == MinCostForQuery(n, a, b)
            invariant j <= i
        {
            if j < |queries| {
                IndexInRange(queries, j);
            }
            j := j + 1;
        }
    }
}
// </vc-code>

