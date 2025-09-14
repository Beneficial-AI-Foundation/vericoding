function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}

// <vc-helpers>
lemma PowerLemma(n: nat)
    ensures Power(n) == (if n == 0 then 1 else Power(n-1) * 2)
{
    if n == 0 {
        assert Power(0) == 1;
    } else {
        calc {
            Power(n);
            2 * Power(n - 1);
            { PowerLemma(n - 1); }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method ComputePower(n: nat) returns (p: nat)
    ensures p == Power(n)
// </vc-spec>
// <vc-code>
{
    var p_val: nat := 1;
    var i: nat := 0;
    while i < n
        invariant i <= n
        invariant p_val == Power(i)
    {
        p_val := p_val * 2;
        i := i + 1;
    }
    p := p_val;
}
// </vc-code>

