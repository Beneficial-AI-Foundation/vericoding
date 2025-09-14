function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method ComputePower(n: nat) returns (p: nat)
    ensures p == Power(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    p := 1;
  } else {
    var p' := ComputePower(n - 1);
    p := 2 * p';
  }
}
// </vc-code>

