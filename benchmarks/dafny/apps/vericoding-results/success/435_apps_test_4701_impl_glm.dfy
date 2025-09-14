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
function MaxOperations(start: int, remaining: int, k: int): int
    requires start >= 1 && k >= 1 && remaining >= 0
    ensures MaxOperations(start, remaining, k) >= start
    decreases remaining
{
    if remaining == 0 then start
    else
        var op1 := start * 2;
        var op2 := start + k;
        var next1 := MaxOperations(op1, remaining-1, k);
        var next2 := MaxOperations(op2, remaining-1, k);
        if next1 >= next2 then next1 else next2
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures result >= 1
// </vc-spec>
// <vc-code>
{
    result := MaxOperations(n, n, k);
}
// </vc-code>

