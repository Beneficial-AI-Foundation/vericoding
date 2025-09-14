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
  ensures Power(n) == (if n == 0 then 1 else 2 * Power(n-1))
{
}

lemma PowerZero()
  ensures Power(0) == 1
{
}

lemma PowerSucc(n: nat)
  requires n > 0
  ensures Power(n) == 2 * Power(n-1)
{
}
// </vc-helpers>

// <vc-spec>
method ComputePower(n:nat) returns (p:nat)
    ensures p == Power(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    p := 1;
  } else {
    var prev := ComputePower(n-1);
    p := 2 * prev;
  }
}
// </vc-code>

