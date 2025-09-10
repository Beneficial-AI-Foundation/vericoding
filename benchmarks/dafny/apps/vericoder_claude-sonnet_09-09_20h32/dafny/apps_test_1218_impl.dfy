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
lemma QuadraticProperties(a: int, x: int)
    ensures (x + 1) * (x + 1) - (x + 1) == x * x + x
{
}

lemma ValidSolutionWhenImpossible(n: int, k: int)
    requires ValidInput(n, k)
    requires ImpossibilityCondition(n, k)
    ensures ValidSolution(n, k, -1)
{
}

lemma ValidSolutionWhenPossible(n: int, k: int, x: int)
    requires ValidInput(n, k)
    requires !ImpossibilityCondition(n, k)
    requires x >= 0
    requires x * x - x + (2 * (n - 1) - k * (k - 1)) <= 0
    requires (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) > 0
    requires k - x >= 0 && k - x <= k
    ensures ValidSolution(n, k, k - x)
{
}

lemma TargetIsNegative(n: int, k: int)
    requires ValidInput(n, k)
    requires !ImpossibilityCondition(n, k)
    ensures 2 * (n - 1) - k * (k - 1) <= 0
{
}

method FindValidX(n: int, k: int) returns (x: int)
    requires ValidInput(n, k)
    requires !ImpossibilityCondition(n, k)
    ensures x >= 0
    ensures x * x - x + (2 * (n - 1) - k * (k - 1)) <= 0
    ensures (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) > 0
    ensures k - x >= 0 && k - x <= k
{
    var target := 2 * (n - 1) - k * (k - 1);
    x := 0;
    
    while x < k
        invariant x >= 0
        invariant x <= k
        decreases k - x
    {
        var current_val := x * x - x + target;
        var next_val := (x + 1) * (x + 1) - (x + 1) + target;
        
        if current_val <= 0 && next_val > 0 {
            return;
        }
        
        x := x + 1;
    }
    
    x := 0;
    
    assert x * x - x + target <= 0;
    TargetIsNegative(n, k);
    assert target <= 0;
    assert (x + 1) * (x + 1) - (x + 1) + target == 1 * 1 - 1 + target == target;
    assert target <= 0;
    assert false;
}
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
        ValidSolutionWhenImpossible(n, k);
        return -1;
    }
    
    var x := FindValidX(n, k);
    result := k - x;
    
    ValidSolutionWhenPossible(n, k, x);
}
// </vc-code>

