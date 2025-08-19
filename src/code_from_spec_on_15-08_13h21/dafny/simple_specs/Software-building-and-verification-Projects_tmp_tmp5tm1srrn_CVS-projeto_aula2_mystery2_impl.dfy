//ATOM

// 3
method mystery1(n: nat,m: nat) returns (res: nat)
 ensures n+m == res
{
  res := 0;
  /* code modified by LLM (iteration 1): Fixed type error by replacing incorrect implication with assignment, and removed assume statement */
  res := n + m;
  return res;
}


//IMPL 

method mystery2(n: nat,m: nat) returns (res: nat)
 ensures n*m == res
{
  res := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant res == i * m
  {
    res := res + m;
    i := i + 1;
  }
}