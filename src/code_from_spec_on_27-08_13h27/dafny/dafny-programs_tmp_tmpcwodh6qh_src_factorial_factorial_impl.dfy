function fact(n: nat): nat 
    ensures fact(n) >= 1
{
    if n == 0 then 1 else n * fact(n - 1)
}

// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method factorial(n: nat) returns (res: nat)
    ensures res == fact(n)
// </vc-spec>
// </vc-spec>

// <vc-code>
method Factorial(n: nat) returns (res: nat)
    ensures res == fact(n)
{
    res := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant res == fact(i)
    {
        i := i + 1;
        res := res * i;
    }
}
// </vc-code>
