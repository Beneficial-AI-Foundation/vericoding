//ATOM
function Power(n:nat):nat 
{
  if n == 0 then 1 else 2 * Power(n-1)
}

//ATOM
method CalcPower(n:nat) returns (p:nat)
  ensures p == 2*n
{
  p := 0;
  assume p == 2*n;
  return p;
}

//IMPL ComputePower
method ComputePower(n:nat) returns (p:nat)
  ensures p == Power(n)
{
  /* code modified by LLM (iteration 1): initialize p to 1 and i to 0 */
  p := 1;
  var i := 0;
  
  /* code modified by LLM (iteration 1): added loop with proper invariants */
  while i < n
    invariant 0 <= i <= n
    invariant p == Power(i)
  {
    /* code modified by LLM (iteration 1): multiply p by 2 and increment i */
    p := p * 2;
    i := i + 1;
  }
}