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

// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == Lucas(n)
// </vc-spec>
// <vc-code>
{
    if n == 1 {
        return 1;
    }
    var a := 2;
    var b := 1;
    var i := 2;

    while i <= n
        invariant 2 <= i <= n+1
        invariant a == Lucas(i-2)
        invariant b == Lucas(i-1)
    {
        a, b := b, a + b;
        i := i + 1;
    }

    return b;
}
// </vc-code>

