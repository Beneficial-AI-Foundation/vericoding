//ATOM
function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}

//IMPL 
method ComputePower(N: int) returns (y: nat) 
  requires N >= 0
  ensures y == Power(N)
{
  y := 1;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant y == Power(i)
  {
    /* code modified by LLM (iteration 1): Added assertion to help Dafny verify that y * 2 equals Power(i + 1) */
    assert y == Power(i);
    assert i + 1 <= N;
    assert Power(i + 1) == 2 * Power(i);
    
    y := y * 2;
    i := i + 1;
    
    /* code modified by LLM (iteration 1): Added assertion to confirm the invariant is maintained */
    assert y == Power(i);
  }
}