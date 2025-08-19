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
    var prev := ComputeFact2(n-1);
    f := n * prev;
  }
}