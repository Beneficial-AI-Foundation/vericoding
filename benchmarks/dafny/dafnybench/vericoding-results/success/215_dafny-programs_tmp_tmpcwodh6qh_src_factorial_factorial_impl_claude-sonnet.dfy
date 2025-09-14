function fact(n: nat): nat 
    ensures fact(n) >= 1
{
    if n == 0 then 1 else n * fact(n - 1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method factorial(n: nat) returns (res: nat)
    ensures res == fact(n)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        res := 1;
    } else {
        var i := 1;
        res := 1;
        while i <= n
            invariant 1 <= i <= n + 1
            invariant res == fact(i - 1)
        {
            res := res * i;
            i := i + 1;
        }
    }
}
// </vc-code>

