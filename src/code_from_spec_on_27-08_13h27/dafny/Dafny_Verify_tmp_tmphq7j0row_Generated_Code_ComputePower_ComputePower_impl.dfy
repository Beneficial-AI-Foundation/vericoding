function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}

// <vc-helpers>
lemma PowerLemma(n: nat)
  ensures Power(n) == if n == 0 then 1 else 2 * Power(n - 1)
{
  // The definition of Power is already recursive and matches the ensures clause,
  // so this lemma is trivially true and serves as a reminder of the definition.
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ComputePower(n: nat) returns (p: nat)
    ensures p == Power(n)
// </vc-spec>
// </vc-spec>

// <vc-code>
method ComputePowerImpl(n: nat) returns (p: nat)
  ensures p == Power(n)
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
