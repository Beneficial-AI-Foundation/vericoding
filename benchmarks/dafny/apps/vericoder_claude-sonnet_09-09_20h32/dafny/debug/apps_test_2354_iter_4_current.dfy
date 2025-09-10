predicate ValidInput(n: int, queries: seq<(int, int)>)
{
    n > 0 && 
    forall i :: 0 <= i < |queries| ==> 1 <= queries[i].0 <= n && 1 <= queries[i].1 <= n
}

function ChessboardValue(n: int, x: int, y: int): int
    requires n > 0
    requires 0 <= x < n && 0 <= y < n
{
    if (x + y) % 2 == 0 then
        1 + (x / 2) * n + (x % 2) * ((n + 1) / 2) + y / 2
    else
        (n * n + 1) / 2 + 1 + (x / 2) * n + (x % 2) * (n / 2) + y / 2
}

predicate ValidResult(n: int, queries: seq<(int, int)>, results: seq<int>)
    requires ValidInput(n, queries)
{
    |results| == |queries| &&
    forall i :: 0 <= i < |queries| ==> 
        var x, y := queries[i].0 - 1, queries[i].1 - 1;
        0 <= x < n && 0 <= y < n &&
        results[i] == ChessboardValue(n, x, y)
}

// <vc-helpers>
lemma ChessboardValueBounds(n: int, x: int, y: int)
    requires n > 0
    requires 0 <= x < n && 0 <= y < n
    ensures 1 <= ChessboardValue(n, x, y) <= n * n
{
    // Split proof into smaller parts
    if (x + y) % 2 == 0 {
        ChessboardValueBoundsEven(n, x, y);
    } else {
        ChessboardValueBoundsOdd(n, x, y);
    }
}

lemma ChessboardValueBoundsEven(n: int, x: int, y: int)
    requires n > 0
    requires 0 <= x < n && 0 <= y < n
    requires (x + y) % 2 == 0
    ensures 1 <= ChessboardValue(n, x, y) <= n * n
{
    var val := 1 + (x / 2) * n + (x % 2) * ((n + 1) / 2) + y / 2;
    
    // Lower bound
    assert val >= 1;
    
    // Upper bound - break down the calculation
    assert x / 2 < n / 2 + 1;
    assert y / 2 < n / 2 + 1;
    assert (x % 2) * ((n + 1) / 2) <= (n + 1) / 2;
    assert (x / 2) * n < n * n;
    
    if n == 1 {
        assert val <= 1;
    } else {
        assert val <= 1 + n * n / 2 + (n + 1) / 2 + n / 2;
        assert val <= n * n;
    }
}

lemma ChessboardValueBoundsOdd(n: int, x: int, y: int)
    requires n > 0
    requires 0 <= x < n && 0 <= y < n
    requires (x + y) % 2 == 1
    ensures 1 <= ChessboardValue(n, x, y) <= n * n
{
    var val := (n * n + 1) / 2 + 1 + (x / 2) * n + (x % 2) * (n / 2) + y / 2;
    
    // Lower bound
    if n == 1 {
        assert val == 1;
    } else {
        assert val >= (n * n + 1) / 2 + 1;
        assert val >= 1;
    }
    
    // Upper bound - simplified approach
    var base := (n * n + 1) / 2 + 1;
    var additional := (x / 2) * n + (x % 2) * (n / 2) + y / 2;
    
    // Bound additional terms
    assert x / 2 <= (n - 1) / 2;
    assert y / 2 <= (n - 1) / 2;
    assert (x % 2) * (n / 2) <= n / 2;
    
    // The maximum value for additional terms
    var max_additional := ((n - 1) / 2) * n + n / 2 + (n - 1) / 2;
    assert additional <= max_additional;
    
    // For the total
    assert val <= base + max_additional;
    
    // Simplify based on parity
    if n % 2 == 0 {
        assert max_additional <= n * n / 2 - 1;
        assert base + max_additional <= n * n;
    } else {
        assert max_additional <= (n * n - 1) / 2;
        assert base + max_additional <= n * n;
    }
}

lemma ValidInputImpliesValidCoordinates(n: int, queries: seq<(int, int)>, i: int)
    requires ValidInput(n, queries)
    requires 0 <= i < |queries|
    ensures var x, y := queries[i].0 - 1, queries[i].1 - 1;
            0 <= x < n && 0 <= y < n
{
    var x, y := queries[i].0 - 1, queries[i].1 - 1;
    assert 1 <= queries[i].0 <= n;
    assert 1 <= queries[i].1 <= n;
    assert 0 <= x < n;
    assert 0 <= y < n;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, queries: seq<(int, int)>) returns (results: seq<int>)
    requires ValidInput(n, queries)
    ensures ValidResult(n, queries, results)
// </vc-spec>
// <vc-code>
{
    results := [];
    
    var i := 0;
    while i < |queries|
        invariant 0 <= i <= |queries|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> 
            var x, y := queries[j].0 - 1, queries[j].1 - 1;
            0 <= x < n && 0 <= y < n &&
            results[j] == ChessboardValue(n, x, y)
    {
        var x := queries[i].0 - 1;
        var y := queries[i].1 - 1;
        
        ValidInputImpliesValidCoordinates(n, queries, i);
        
        var value := ChessboardValue(n, x, y);
        results := results + [value];
        
        i := i + 1;
    }
}
// </vc-code>

