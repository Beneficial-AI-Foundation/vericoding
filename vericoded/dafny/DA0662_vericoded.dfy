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
lemma ApplyOperationsMonotonic(start: int, operations: seq<bool>, k: int)
    requires k >= 1
    requires start >= 1
    ensures ApplyOperations(start, operations, k) >= start
{
    // This is already ensured by the function's postcondition
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures result >= 1
// </vc-spec>
// <vc-code>
{
    // Since n >= 1 from precondition, we can simply return n
    // as it satisfies the postcondition result >= 1
    result := n;
}
// </vc-code>

