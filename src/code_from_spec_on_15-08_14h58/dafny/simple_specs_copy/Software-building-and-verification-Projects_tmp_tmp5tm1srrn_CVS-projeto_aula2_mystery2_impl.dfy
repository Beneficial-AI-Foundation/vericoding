//ATOM

// 3
method mystery1(n: nat,m: nat) returns (res: nat)
 ensures n+m == res
{
  /* code modified by LLM (iteration 1): Fixed compilation errors by removing invalid assume statement and implementing correct logic */
  res := n + m;
}


//IMPL mystery2

method mystery2(n: nat,m: nat) returns (res: nat)
 ensures n*m == res
{
  /* code modified by LLM (iteration 1): Implementation already correct, just added proper header */
  res := n * m;
}