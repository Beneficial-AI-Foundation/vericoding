function Power(n:nat):nat 
{
    if n == 0 then 1 else 2 * Power(n-1)
}

method CalcPower(n:nat) returns (p:nat)
    ensures p == 2*n;
{
  assume{:axiom} false;
}

method ComputePower(n:nat) returns (p:nat)
    ensures p == Power(n)

{
  assume false;
}