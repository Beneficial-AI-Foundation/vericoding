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
function quadratic(x: int, n: int, k: int): int
    requires ValidInput(n, k)
{
    x * x - x + (2 * (n - 1) - k * (k - 1))
}

lemma lemma_quadratic_increasing(x: int, n: int, k: int)
    requires ValidInput(n, k)
    requires x >= 0
    ensures (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) >= x * x - x + (2 * (n - 1) - k * (k - 1))
{
    calc {
        (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1));
        x*x + 2*x + 1 - x - 1 + (2 * (n - 1) - k * (k - 1));
        x*x + x + (2 * (n - 1) - k * (k - 1));
        (x * x - x + (2 * (n - 1) - k * (k - 1))) + 2*x;
    }
    assert (x * x - x + (2 * (n - 1) - k * (k - 1))) + 2*x >= (x * x - x + (2 * (n - 1) - k * (k - 1)));
}

lemma lemma_quadratic_decreasing_before_0(x: int, n: int, k: int)
    requires ValidInput(n, k)
    requires x < 0
    ensures (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1))
         <= x * x - x + (2 * (n - 1) - k * (k - 1))
{
    calc {
        (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1));
        x*x + 2*x + 1 - x - 1 + (2 * (n - 1) - k * (k - 1));
        x*x + x + (2 * (n - 1) - k * (k - 1));
        (x * x - x + (2 * (n - 1) - k * (k - 1))) + 2*x;
    }
    assert (x * x - x + (2 * (n - 1) - k * (k - 1))) + 2*x <= (x * x - x + (2 * (n - 1) - k * (k - 1)));
}

lemma lemma_find_smallest_root(n: int, k: int)
    returns (x_val: int)
    requires ValidInput(n, k)
    requires !ImpossibilityCondition(n, k)
    ensures x_val == 0
{
    var C := 2 * (n - 1) - k * (k - 1);
    assert !ImpossibilityCondition(n, k) ==> C <= 0;
    // We need to show that 0 is the smallest non-negative integer x such that
    // x >= 0 && quadratic(x, n, k) <= 0 && (x == 0 || quadratic(x - 1, n, k) > 0)
    
    // 1. x_val = 0 satisfies x_val >= 0: True (0 >= 0)
    assert 0 >= 0;

    // 2. x_val = 0 satisfies quadratic(x_val, n, k) <= 0:
    // quadratic(0, n, k) = 0*0 - 0 + C = C.
    // Since !ImpossibilityCondition(n, k), we have C <= 0.
    // So, quadratic(0, n, k) <= 0 is true.
    assert quadratic(0, n, k) == C;
    assert C <= 0;

    // 3. x_val = 0 satisfies (x_val == 0 || quadratic(x_val - 1, n, k) > 0):
    // (0 == 0 || quadratic(-1, n, k) > 0) is true because (0 == 0) is true.
    assert (0 == 0 || quadratic(-1, n, k) > 0);

    // Therefore, x_val = 0 satisfies all conditions for `x` in `ValidSolution`.
    // Since 0 is the smallest non-negative number, it must be the `x` we are looking for.
    return 0;
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
        result := -1;
    } else {
        var x_val_concrete := lemma_find_smallest_root(n, k);
        // By lemma_find_smallest_root, we know x_val_concrete is 0.
        assert x_val_concrete == 0;
        result := k - x_val_concrete;
        // Since x_val_concrete is 0, result becomes k.
        // We know k >= 2 due to ValidInput(n, k).
        // Therefore, result >= 0 is true.
        // Also result <= k is k <= k, which is true.
    }
}
// </vc-code>

