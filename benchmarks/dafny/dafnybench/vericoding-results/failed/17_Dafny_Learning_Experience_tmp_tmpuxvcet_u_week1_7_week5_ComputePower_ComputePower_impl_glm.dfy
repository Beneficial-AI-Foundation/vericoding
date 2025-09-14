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

// </vc-helpers>

// <vc-spec>
method ComputePower(n:nat) returns (p:nat)
    ensures p == Power(n)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var result := 1;
  while i < n
      invariant 0 <= i <= n
      invariant result == Power(i)
  {
      result := 2 * result;
      i := i + 1;
  }
  p := result;
}
// </vc-code>

