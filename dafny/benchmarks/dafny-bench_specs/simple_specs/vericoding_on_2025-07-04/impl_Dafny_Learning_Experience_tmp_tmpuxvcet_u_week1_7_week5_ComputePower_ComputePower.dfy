//ATOM
function Power(n:nat):nat 
{
  if n == 0 then 1 else 2 * Power(n-1)
}

//ATOM
method CalcPower(n:nat) returns (p:nat)
  ensures p == 2*n
{
  /* code modified by LLM (iteration 1): fixed syntax error - changed invalid assume statement to simple assignment */
  p := 2*n;
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
    /* code modified by LLM (iteration 1): added decreases clause to ensure termination */
    decreases n - i
  {
    /* code modified by LLM (iteration 1): added assertion to help verification understand the Power function relationship */
    assert Power(i + 1) == 2 * Power(i);
    p := p * 2;
    i := i + 1;
  }
}