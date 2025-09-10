function Lucas(n: int): int
    requires n >= 0
{
    if n == 0 then 2
    else if n == 1 then 1
    else Lucas(n-1) + Lucas(n-2)
}

predicate ValidInput(n: int) {
    1 <= n <= 86
}

// <vc-helpers>
function LucasRec(n: int): int
    requires n >= 0
    decreases n
{
    if n == 0 then 2
    else if n == 1 then 1
    else LucasRec(n-1) + LucasRec(n-2)
}
// The `ValidInput` predicate is already defined in the preamble, so it should not be redefined here.
// predicate ValidInput(n: int) {
//     1 <= n <= 86
// }
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == Lucas(n)
// </vc-spec>
// <vc-code>
{
    var a := 2; // LucasRec(0)
    var b := 1; // LucasRec(1)
    if n == 0 {
        return a;
    }
    if n == 1 {
        return b;
    }
    var i := 2;
    while i <= n
        invariant 2 <= i <= n + 1
        invariant a == LucasRec(i - 2)
        invariant b == LucasRec(i - 1)
        decreases n - i
    {
        var next_val := a + b;
        a := b;
        b := next_val;
        i := i + 1;
    }
    return b;
}
// </vc-code>

