//ATOM
function C(n: nat): nat 
{
  if n == 0 then 1 else (4 * n - 2) * C(n-1) / (n + 1) 
}

//IMPL 
method calcC(n: nat) returns (res: nat)
  ensures res == C(n)
{
  if n == 0 {
    res := 1;
  } else {
    res := 1;
    var i := 1;
    while i <= n
      invariant 1 <= i <= n + 1
      invariant res == C(i - 1)
    {
      res := (4 * i - 2) * res / (i + 1);
      i := i + 1;
    }
  }
}