function Power(n:nat):nat 
{
    if n == 0 then 1 else 2 * Power(n-1)
}

method CalcPower(n:nat) returns (p:nat)
    ensures p == 2*n;
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma PowerIterative(n: nat, i: nat, acc: nat)
    requires acc == Power(i)
    requires i <= n
    ensures acc * Power(n - i) == Power(n)
    decreases n - i
{
    if i == n {
        assert acc * Power(n - i) == acc * Power(0) == acc * 1 == acc == Power(n);
    } else {
        PowerIterative(n, i + 1, acc * 2);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ComputePower(n:nat) returns (p:nat)
    ensures p == Power(n)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    p := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant p == Power(i)
    {
        p := p * 2;
        i := i + 1;
    }
}
// </vc-code>
