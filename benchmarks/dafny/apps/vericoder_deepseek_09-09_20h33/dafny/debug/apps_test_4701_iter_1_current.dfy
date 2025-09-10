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
    {
        operations := operations + [true];
        result := result / 2;
    }
}
// </vc-code>

