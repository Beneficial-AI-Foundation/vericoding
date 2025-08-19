//ATOM
function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}

//IMPL ComputePower
method ComputePower(N: int) returns (y: nat)
  requires N >= 0
  ensures y == Power(N)
{
  /* code modified by LLM (iteration 1): removed invalid markdown comments and fixed implementation */
  if N == 0 {
    y := 1;
  } else {
    y := 1;
    var i := 0;
    while i < N
      invariant 0 <= i <= N
      invariant y == Power(i)
    {
      y := 2 * y;
      i := i + 1;
    }
  }
}