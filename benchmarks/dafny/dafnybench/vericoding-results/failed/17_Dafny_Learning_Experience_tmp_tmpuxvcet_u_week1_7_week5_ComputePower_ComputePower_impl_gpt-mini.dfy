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
lemma PowerStep(m:nat)
  ensures Power(m+1) == 2 * Power(m)
  decreases m
{
  if m == 0 {
    assert Power(0) == 1;
    assert Power(1) == 2 * Power(0);
  } else {
    PowerStep(m-1);
    assert Power(m+1) == 2 * Power(m);
  }
}
// </vc-helpers>

// <vc-spec>
method ComputePower(n:nat) returns (p:nat)
    ensures p == Power(n)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  p := 1;
  while i < n
    invariant 0 <= i <= n
    invariant p == Power(i)
  {
    var oldi := i;
    PowerStep(oldi);
    p := 2 * p;
    i := i + 1;
    assert p == Power(i);
  }
}
// </vc-code>

