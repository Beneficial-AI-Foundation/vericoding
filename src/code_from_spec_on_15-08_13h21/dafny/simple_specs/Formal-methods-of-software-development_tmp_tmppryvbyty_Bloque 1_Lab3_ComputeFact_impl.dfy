//ATOM

function factorial(n:int):int
requires n>=0
{
  if n==0 || n==1 then 1 else n*factorial(n-1)
}


//IMPL 

// PROGRAMA VERIFICADOR DE WHILE
method ComputeFact (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)

{
  f := 1;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant f == factorial(i)
  {
    i := i + 1;
    f := f * i;
  }
}