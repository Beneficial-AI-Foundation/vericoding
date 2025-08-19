//ATOM

function factorial(n:int):int
requires n>=0
{
  if n==0 || n==1 then 1 else n*factorial(n-1)
}


// SPEC

method ComputeFact2 (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)
{
}