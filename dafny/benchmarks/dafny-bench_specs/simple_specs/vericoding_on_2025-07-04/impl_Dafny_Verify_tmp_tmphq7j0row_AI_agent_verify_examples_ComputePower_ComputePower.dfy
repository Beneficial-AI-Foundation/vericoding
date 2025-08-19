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
      /* code modified by LLM (iteration 1): Added assertion to help Dafny verify that 2 * Power(i) equals Power(i + 1) */
      assert i + 1 > 0;
      assert Power(i + 1) == 2 * Power(i);
      y := 2 * y;
      i := i + 1;
    }
  }
}