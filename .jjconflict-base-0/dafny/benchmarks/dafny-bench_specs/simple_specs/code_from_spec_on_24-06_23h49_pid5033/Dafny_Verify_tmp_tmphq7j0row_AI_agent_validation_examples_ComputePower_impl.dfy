//ATOM
function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}

//IMPL
method ComputePower(N: int) returns (y: nat) 
  requires N >= 0
  ensures y == Power(N)
{
  if N == 0 {
    y := 1;
  } else {
    y := 1;
    var i := 0;
    while i < N
      invariant 0 <= i <= N
      invariant y == Power(i)
    {
      /* code modified by LLM (iteration 1): update y first to maintain invariant, then increment i */
      y := y * 2;
      i := i + 1;
    }
  }
}