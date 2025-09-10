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
lemma LucasIterative(n: int, i: int, a: int, b: int)
    requires 0 <= i < n
    requires a == Lucas(i)
    requires b == Lucas(i+1)
    ensures Lucas(i+2) == a + b
{
    // By definition of Lucas function:
    // Lucas(i+2) = Lucas(i+1) + Lucas(i) = b + a = a + b
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == Lucas(n)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 2;
    }
    if n == 1 {
        return 1;
    }
    
    var a := 2;  // Lucas(0)
    var b := 1;  // Lucas(1)
    var i := 1;
    
    while i < n
        invariant 1 <= i <= n
        invariant a == Lucas(i-1)
        invariant b == Lucas(i)
    {
        LucasIterative(n, i-1, a, b);
        var temp := a + b;
        a := b;
        b := temp;
        i := i + 1;
    }
    
    return b;
}
// </vc-code>

