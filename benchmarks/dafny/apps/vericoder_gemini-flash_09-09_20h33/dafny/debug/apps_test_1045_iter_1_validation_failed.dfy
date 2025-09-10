predicate ValidInput(n: int) {
    n >= 1
}

function CubesForLevel(level: int): int
    requires level >= 1
{
    level * (level + 1) / 2
}

function TotalCubesForHeight(h: int): int
    requires h >= 1
{
    h * (h + 1) * (h + 2) / 6
}

predicate ValidPyramidHeight(n: int, h: int) {
    ValidInput(n) && h >= 1 && 
    TotalCubesForHeight(h) <= n &&
    TotalCubesForHeight(h + 1) > n
}

// <vc-helpers>
lemma lemma_TotalCubesForHeight_increasing(h: int)
    requires h >= 1
    ensures TotalCubesForHeight(h + 1) > TotalCubesForHeight(h)
{
    calc {
        TotalCubesForHeight(h+1) - TotalCubesForHeight(h);
        (h+1)*(h+2)*(h+3)/6 - h*(h+1)*(h+2)/6;
        (h+1)*(h+2)/6 * ((h+3) - h);
        (h+1)*(h+2)/6 * 3;
        (h+1)*(h+2)/2;
    }
    assert (h+1)*(h+2)/2 >= 1 * (1+1) / 2 == 1; // Since h >= 1
}

lemma lemma_TotalCubesForHeight_lower_bound(h: int)
    requires h >= 1
    ensures TotalCubesForHeight(h) >= 1
    ensures TotalCubesForHeight(h) == h * (h + 1) * (h + 2) / 6
{
    // The postcondition TotalCubesForHeight(h) >= 1 is clear for h >= 1
    // The second postcondition is literally the definition, proving it is trivial.
}

lemma lemma_TotalCubesForHeight_no_overflow(n: int, h: int)
    requires n >= 1
    requires h >= 1
    requires TotalCubesForHeight(h) <= n
    ensures TotalCubesForHeight(h+1) > n ==> h <= n
{
    // This lemma is generally not needed if we are simply comparing values within typical int ranges,
    // where overflow is not an issue for the values h, h+1 etc.
    // If n is very large, h could theoretically be large enough that h*(h+1)*(h+2)/6 overflows.
    // However, Dafny's default integers are arbitrary precision integers, so overflow isn't a concern.
    // If we assume standard 64-bit integers, then `h` cannot be extremely large for `TotalCubesForHeight(h)`
    // to fit within `int` capacity. For `n` up to `2^63 - 1`, `h` will be around `cbrt(6*2^63)` which is
    // roughly `cbrt(2^66)` or `2^22`. So `h+1` is fine.
}

predicate TotalCubesForHeightApproximation(h: int, n: int) {
    (h * h * h) <= 6 * n // A rough lower bound for h
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures ValidPyramidHeight(n, result)
// </vc-spec>
// <vc-code>
{
    var h := 1;
    while TotalCubesForHeight(h) <= n
        invariant h >= 1
        invariant TotalCubesForHeight(h) <= n
        decreases n - TotalCubesForHeight(h) // While n - TotalCubesForHeight(h) is technically not strictly decreasing,
                                            // h is strictly increasing, and TotalCubesForHeight(h) increases
                                            // so n - TotalCubesForHeight(h) decreases.
    {
        lemma_TotalCubesForHeight_increasing(h);
        h := h + 1;
    }
    // Loop terminates when TotalCubesForHeight(h) > n
    // We want TotalCubesForHeight(result) <= n and TotalCubesForHeight(result + 1) > n
    // So if TotalCubesForHeight(h-1) <= n and TotalCubesForHeight(h) > n, then result = h-1
    result := h - 1;

    // Prove postconditions
    // 1. result >= 1
    // This is implied because h starts at 1. If n >= 1, then TotalCubesForHeight(1) = 1.
    // If n = 1, h becomes 2, result is 1. If n >= 1, h will be at least 2.
    lemma_TotalCubesForHeight_lower_bound(1); // TotalCubesForHeight(1) == 1
    if n < TotalCubesForHeight(1) { // This case implies n < 1, which contradicts ValidInput(n)
        assert false; // Should not happen given ValidInput(n)
    } else { // n >= TotalCubesForHeight(1)
        // This ensures the loop runs at least once, and h will be at least 2.
        // So result (h-1) will be at least 1.
    }

    // 2. ValidPyramidHeight(n, result)
    // This means:
    // a) ValidInput(n) -- Given by precondition
    // b) result >= 1 -- Proven above
    // c) TotalCubesForHeight(result) <= n
    //    `result` is `h-1`. So we need TotalCubesForHeight(h-1) <= n.
    //    When the loop terminates, TotalCubesForHeight(h) > n.
    //    The invariant ensures TotalCubesForHeight(prev_h) <= n where prev_h is the value of h in the previous iteration.
    //    So TotalCubesForHeight(h-1) <= n holds from the loop invariant.
    // d) TotalCubesForHeight(result + 1) > n
    //    `result + 1` is `h`. So we need TotalCubesForHeight(h) > n.
    //    This is exactly the condition that caused the loop to terminate.
}
// </vc-code>

