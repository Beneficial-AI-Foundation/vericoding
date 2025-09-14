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
function Power(n:nat):nat 
    decreases n
{
    if n == 0 then 1 else 2 * Power(n-1)
}
// No additional helpers needed; the recursive function Power is already defined and the loop invariant uses it directly.
// </vc-helpers>

// <vc-spec>
method ComputePower(n:nat) returns (p:nat)
    ensures p == Power(n)
// </vc-spec>
// <vc-code>
{
  p := 1;
  var i := 0;
  while i < n decreases n-i
    invariant 0 <= i <= n
    invariant p == Power(i)
  {
    p := p * 2;
    i := i + 1;
  }
}
// </vc-code>

