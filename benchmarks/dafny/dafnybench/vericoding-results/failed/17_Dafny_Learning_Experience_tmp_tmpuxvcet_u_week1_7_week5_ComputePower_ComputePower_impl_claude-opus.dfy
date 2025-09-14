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
lemma PowerLemma(n: nat)
    ensures Power(n + 1) == 2 * Power(n)
{
    // This follows directly from the definition of Power
}
// </vc-helpers>

// <vc-spec>
method ComputePower(n:nat) returns (p:nat)
    ensures p == Power(n)
// </vc-spec>
// <vc-code>
{
    p := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant p == Power(i)
    {
        PowerLemma(i);
        p := 2 * p;
        i := i + 1;
    }
}
// </vc-code>

