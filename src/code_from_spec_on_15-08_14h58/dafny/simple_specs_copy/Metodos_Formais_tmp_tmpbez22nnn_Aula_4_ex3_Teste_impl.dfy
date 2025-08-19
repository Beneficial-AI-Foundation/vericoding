function Fib(n:nat):nat
{
  if n < 2
  then n
  else Fib(n-2) + Fib(n-1)
}


//ATOM

method ComputeFib(n:nat) returns (x:nat)
ensures x == Fib(n)
{
  x := 0;
  assume x == Fib(n);
  return x;
}


//IMPL 

method Teste()
{
}