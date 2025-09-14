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
lemma ApplyOperationsPreservesPositive(start: int, operations: seq<bool>, k: int)
    requires k >= 1
    requires start >= 1
    ensures ApplyOperations(start, operations, k) >= 1
    decreases |operations|
{
    if |operations| == 0 {
        // Base case: start >= 1
    } else if operations[0] {
        // Multiplication case: start * 2 >= 2 >= 1
        ApplyOperationsPreservesPositive(start * 2, operations[1..], k);
    } else {
        // Addition case: start + k >= 1 + 1 = 2 >= 1
        ApplyOperationsPreservesPositive(start + k, operations[1..], k);
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
    ApplyOperationsPreservesPositive(n, [], k);
    result := ApplyOperations(n, [], k);
}
// </vc-code>

