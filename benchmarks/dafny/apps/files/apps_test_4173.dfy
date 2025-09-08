Find the minimum cost to purchase exactly n liters of water using 1-liter bottles 
(costing a burles each) and 2-liter bottles (costing b burles each), with infinite 
supply of both types available. Process multiple queries efficiently.

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
{
    results := [];
    for i := 0 to |queries|
        invariant |results| == i
        invariant forall j | 0 <= j < i :: 
            var n := queries[j].0;
            var a := queries[j].1;
            var b := queries[j].2;
            results[j] == (if n % 2 == 0 then
                if n * a <= (n / 2) * b then n * a else (n / 2) * b
            else
                if n * a <= (n / 2) * b + a then n * a else (n / 2) * b + a)
    {
        var n := queries[i].0;
        var a := queries[i].1; 
        var b := queries[i].2;

        var cost: int;
        if n % 2 == 0 {
            var allOneLiter := n * a;
            var allTwoLiter := (n / 2) * b;
            cost := if allOneLiter <= allTwoLiter then allOneLiter else allTwoLiter;
        } else {
            var allOneLiter := n * a;
            var mixedBottles := (n / 2) * b + a;
            cost := if allOneLiter <= mixedBottles then allOneLiter else mixedBottles;
        }

        results := results + [cost];
    }
}
