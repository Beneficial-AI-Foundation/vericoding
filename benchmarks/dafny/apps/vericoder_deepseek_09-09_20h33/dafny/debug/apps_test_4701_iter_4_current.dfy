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
            var rest := operations[1..];
            LemmaApplyOperationsTrue(n * 2, rest, k);
            assert ApplyOperations(n, operations + [true], k) == ApplyOperations(n * 2, rest + [true], k);
            assert ApplyOperations(n * 2, rest + [true], k) == ApplyOperations(n * 2, rest, k) / 2;
            assert ApplyOperations(n * 2, rest, k) == ApplyOperations(n, operations, k);
        } else {
            var rest := operations[1..];
            LemmaApplyOperationsTrue(n + k, rest, k);
            assert ApplyOperations(n, operations + [true], k) == ApplyOperations(n + k, rest + [true], k);
            assert ApplyOperations(n + k, rest + [true], k) == ApplyOperations(n + k, rest, k) / 2;
            assert ApplyOperations(n + k, rest, k) == ApplyOperations(n, operations, k);
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
        LemmaApplyOperationsMonotonic(n, operations, k);
    }
}
// </vc-code>

