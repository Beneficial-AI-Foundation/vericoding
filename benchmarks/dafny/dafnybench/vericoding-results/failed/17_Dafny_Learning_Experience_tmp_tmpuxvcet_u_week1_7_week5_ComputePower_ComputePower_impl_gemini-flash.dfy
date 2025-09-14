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
// The original Power function is moved to the top of the file.
// No additional helpers needed here.
// </vc-helpers>

// <vc-spec>
method ComputePower(n:nat) returns (p:nat)
    ensures p == Power(n)
// </vc-spec>
// <vc-code>
{
  var p_local := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant p_local == Power(i)
  {
    p_local := p_local * 2;
    i := i + 1;
  }
  return p_local;
}
// </vc-code>

