predicate ValidInput(n: int, k: int)
{
    n >= 1 && k >= 1
}

function ApplyOperations(start: int, operations: seq<bool>, k: int): int
    requires k >= 1
    requires start >= 1
    ensures ApplyOperations(start, operations, k) >= start
    decreases |operations|
{
    if |operations| == 0 then start
    else if operations[0] then ApplyOperations(start * 2, operations[1..], k)
    else ApplyOperations(start + k, operations[1..], k)
}

// <vc-helpers>
lemma LemmaApplyOperationsMonotonic(start: int, operations: seq<bool>, k: int)
    requires k >= 1
    requires start >= 1
    ensures ApplyOperations(start, operations, k) >= start
    decreases |operations|
{
    if |operations| == 0 {
    } else {
        if operations[0] {
            LemmaApplyOperationsMonotonic(start * 2, operations[1..], k);
        } else {
            LemmaApplyOperationsMonotonic(start + k, operations[1..], k);
        }
    }
}

lemma LemmaApplyOperationsNonNegative(start: int, operations: seq<bool>, k: int)
    requires k >= 1
    requires start >= 1
    ensures ApplyOperations(start, operations, k) >= 1
    decreases |operations|
{
    if |operations| == 0 {
    } else {
        if operations[0] {
            assert start * 2 >= 2;
            LemmaApplyOperationsNonNegative(start * 2, operations[1..], k);
        } else {
            assert start + k >= 1 + k >= 2;
            LemmaApplyOperationsNonNegative(start + k, operations[1..], k);
        }
    }
}

lemma LemmaResultDecreases(result: int, operations: seq<bool>, k: int, n: int)
    requires result >= 1
    requires result == ApplyOperations(n, operations, k)
    requires result % 2 == 0
    ensures (result / 2) < result
{
}

lemma LemmaApplyOperationsTrue(n: int, operations: seq<bool>, k: int)
    requires k >= 1
    requires n >= 1
    requires ApplyOperations(n, operations, k) % 2 == 0
    ensures ApplyOperations(n, operations + [true], k) == ApplyOperations(n, operations, k) / 2
    decreases |operations|
{
    if |operations| == 0 {
        assert ApplyOperations(n, [true], k) == n * 2;
        assert n * 2 / 2 == n;
        assert ApplyOperations(n, [], k) == n;
    } else {
        if operations[0] {
            LemmaApplyOperationsTrue(n * 2, operations[1..], k);
        } else {
            LemmaApplyOperationsTrue(n + k, operations[1..], k);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures result >= 1
// </vc-spec>
// <vc-code>
{
    result := n;
    var operations: seq<bool> := [];
    
    while result % 2 == 0
        invariant result >= 1
        invariant result == ApplyOperations(n, operations, k)
        decreases result
    {
        LemmaApplyOperationsTrue(n, operations, k);
        operations := operations + [true];
        result := result / 2;
    }
}
// </vc-code>

