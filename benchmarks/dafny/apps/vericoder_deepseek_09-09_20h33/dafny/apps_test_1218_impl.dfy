predicate ValidInput(n: int, k: int) {
    n >= 1 && k >= 2
}

function ImpossibilityCondition(n: int, k: int): bool
    requires ValidInput(n, k)
{
    2 * (n - 1) - k * (k - 1) > 0
}

predicate ValidSolution(n: int, k: int, result: int)
    requires ValidInput(n, k)
{
    if ImpossibilityCondition(n, k) then
        result == -1
    else
        result >= 0 && result <= k &&
        exists x: int :: 
            x >= 0 && 
            x * x - x + (2 * (n - 1) - k * (k - 1)) <= 0 && 
            (x == 0 || (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) > 0) &&
            result == k - x
}

// <vc-helpers>
lemma QuadraticRootLemma(n: int, k: int)
    requires ValidInput(n, k)
    requires !ImpossibilityCondition(n, k)
    ensures exists x: int :: 
        x >= 0 && 
        x * x - x + (2 * (n - 1) - k * (k - 1)) <= 0 && 
        (x == 0 || (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) > 0)
{
    // Use integer arithmetic instead of real operations
    var discriminant := 1 - 4 * (2 * (n - 1) - k * (k - 1));
    assert discriminant >= 0;
    
    var x := 0;
    while (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) <= 0
        invariant x >= 0
    {
        x := x + 1;
    }
    
    assert x >= 0;
    assert x * x - x + (2 * (n - 1) - k * (k - 1)) <= 0;
    assert (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) > 0;
}

ghost function FindMinimalX(n: int, k: int): int
    requires ValidInput(n, k)
    requires !ImpossibilityCondition(n, k)
    ensures result >= 0
    ensures result * result - result + (2 * (n - 1) - k * (k - 1)) <= 0
    ensures result == 0 || (result + 1) * (result + 1) - (result + 1) + (2 * (n - 1) - k * (k - 1)) > 0
{
    QuadraticRootLemma(n, k);
    var candidate := 0;
    while (candidate + 1) * (candidate + 1) - (candidate + 1) + (2 * (n - 1) - k * (k - 1)) <= 0
        invariant candidate >= 0
    {
        candidate := candidate + 1;
    }
    candidate
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures result >= -1
    ensures (result == -1) <==> ImpossibilityCondition(n, k)
    ensures ValidSolution(n, k, result)
// </vc-spec>
// <vc-code>
{
    if ImpossibilityCondition(n, k) {
        result := -1;
    } else {
        ghost var x := FindMinimalX(n, k);
        result := k - x;
    }
}
// </vc-code>

