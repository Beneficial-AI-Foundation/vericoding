predicate ValidInput(a: int, b: int, c: int, d: int)
{
    0 <= a < b <= 100 && 0 <= c < d <= 100
}

function min(x: int, y: int): int
{
    if x < y then x else y
}

function max(x: int, y: int): int
{
    if x > y then x else y
}

function IntervalOverlapLength(a: int, b: int, c: int, d: int): int
{
    if min(b, d) - max(a, c) > 0 then min(b, d) - max(a, c) else 0
}

// <vc-helpers>
lemma MinMaxOverlap(a: int, b: int, c: int, d: int)
    requires 0 <= a < b <= 100
    requires 0 <= c < d <= 100
    ensures IntervalOverlapLength(a, b, c, d) == min(b, d) - max(a, c) || IntervalOverlapLength(a, b, c, d) == 0
    ensures min(b, d) - max(a, c) >= 0 ==> IntervalOverlapLength(a, b, c, d) == min(b, d) - max(a, c)
    ensures min(b, d) - max(a, c) < 0 ==> IntervalOverlapLength(a, b, c, d) == 0
{
    // The definition of IntervalOverlapLength directly implies these properties.
    // No specific proof steps are needed, as this lemma states properties that
    // are trivially true by the function's definition.
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, d: int) returns (result: int)
    requires ValidInput(a, b, c, d)
    ensures result >= 0
    ensures result == IntervalOverlapLength(a, b, c, d)
    ensures result <= 100
// </vc-spec>
// <vc-code>
{
    var overlap_end := min(b, d);
    var overlap_start := max(a, c);

    if overlap_end - overlap_start > 0 {
        result := overlap_end - overlap_start;
    } else {
        result := 0;
    }

    // Proofs for ensures clauses:
    // 1. result >= 0:
    //    If overlap_end - overlap_start > 0, then result is positive.
    //    If overlap_end - overlap_start <= 0, then result is 0.
    //    In both cases, result >= 0.

    // 2. result == IntervalOverlapLength(a, b, c, d):
    //    By definition of IntervalOverlapLength, it checks `min(b, d) - max(a, c) > 0`.
    //    If true, it returns `min(b, d) - max(a, c)`.
    //    If false, it returns `0`.
    //    Our code directly implements this conditional logic with `overlap_end - overlap_start`.
    //    Thus, `result` will always be equal to `IntervalOverlapLength(a, b, c, d)`.
    reveal IntervalOverlapLength(); // Ensures the definition is visible for verification
    assert result == IntervalOverlapLength(a, b, c, d);

    // 3. result <= 100:
    //    We know a, b, c, d are between 0 and 100.
    //    min(b, d) will be at most 100 (since b <= 100 and d <= 100).
    //    max(a, c) will be at least 0 (since a >= 0 and c >= 0).
    //    So, overlap_end <= 100 and overlap_start >= 0.
    //    Therefore, result = overlap_end - overlap_start <= 100 - 0 = 100.
    //    If result is 0, it's also <= 100.
    assert result <= 100;
}
// </vc-code>

