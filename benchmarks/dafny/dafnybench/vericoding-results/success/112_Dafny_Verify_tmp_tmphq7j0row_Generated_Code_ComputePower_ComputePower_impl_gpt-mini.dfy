function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}

// <vc-helpers>
lemma Power_Succ(k: nat)
  ensures Power(k + 1) == 2 * Power(k)
{
  assert Power(k + 1) == 2 * Power(k);
}

lemma SubIsNat(n: nat, i: nat)
  requires i <= n
  ensures n - i >= 0
{
  assert n - i >= 0;
}
// </vc-helpers>

// <vc-spec>
method ComputePower(n: nat) returns (p: nat)
    ensures p == Power(n)
// </vc-spec>
// <vc-code>
{
  p := 1;
  var i: nat := n;
  while i > 0
    invariant i <= n
    invariant p == Power(n - i)
    decreases i
  {
    SubIsNat(n, i);
    Power_Succ(n - i);
    p := 2 * p;
    i := i - 1;
  }
  assert i == 0;
}
// </vc-code>

