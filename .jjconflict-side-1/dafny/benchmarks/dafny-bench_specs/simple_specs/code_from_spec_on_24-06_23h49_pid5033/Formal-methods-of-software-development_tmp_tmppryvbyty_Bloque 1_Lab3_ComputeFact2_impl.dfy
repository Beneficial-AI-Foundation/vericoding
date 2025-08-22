//ATOM

function factorial(n:int):int
requires n>=0
{
  if n==0 || n==1 then 1 else n*factorial(n-1)
}

//IMPL ComputeFact2

method ComputeFact2 (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)
{
  if n == 0 || n == 1 {
    f := 1;
  } else {
    f := 1;
    var i := 2;
    while i <= n
      invariant 2 <= i <= n + 1
      invariant f == factorial(i - 1)
    {
      f := f * i;
      i := i + 1;
    }
  }
}