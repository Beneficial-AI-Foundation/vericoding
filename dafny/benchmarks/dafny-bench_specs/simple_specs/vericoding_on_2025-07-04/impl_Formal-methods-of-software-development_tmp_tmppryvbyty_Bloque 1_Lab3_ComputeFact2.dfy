//ATOM

function factorial(n:int):int
requires n>=0
{
  if n==0 || n==1 then 1 else n*factorial(n-1)
}

//IMPL 

method ComputeFact2 (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)
{
  if n == 0 || n == 1 {
    f := 1;
  } else {
    var i := 2;
    f := 1;
    while i <= n
      invariant 1 <= i <= n + 1
      invariant f == factorial(i - 1)
    {
      f := f * i;
      i := i + 1;
    }
  }
}