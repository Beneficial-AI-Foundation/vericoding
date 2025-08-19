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
    /* code modified by LLM (iteration 1): loop body unchanged, compilation error was due to invalid text at file start */
    y := y * 2;
    i := i + 1;
  }
}