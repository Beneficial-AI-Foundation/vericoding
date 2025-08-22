//ATOM mystery1
method mystery1(n: nat,m: nat) returns (res: nat)
 ensures n+m == res
{
  /* code modified by LLM (iteration 1): fixed assume statement syntax */
  res := n + m;
}

//IMPL mystery2
method mystery2(n: nat,m: nat) returns (res: nat)
 ensures n*m == res
{
  res := n * m;
}