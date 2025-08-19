//ATOM

// 3
method mystery1(n: nat,m: nat) returns (res: nat)
 ensures n+m == res
{
  res := 0;
  assume n+m ==> res;
  return res;
}


// SPEC

method mystery2(n: nat,m: nat) returns (res: nat)
 ensures n*m == res
{
}