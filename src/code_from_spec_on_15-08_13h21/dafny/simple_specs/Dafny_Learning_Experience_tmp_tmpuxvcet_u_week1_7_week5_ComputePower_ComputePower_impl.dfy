function Power(n:nat):nat 
{
  if n == 0 then 1 else 2 * Power(n-1)
}


//ATOM

method CalcPower(n:nat) returns (p:nat)
  ensures p == 2*n
{
  /* code modified by LLM (iteration 1): Fixed syntax error - changed assume statement to proper assignment */
  p := 2*n;
  return p;
}


//IMPL 

method ComputePower(n:nat) returns (p:nat)
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