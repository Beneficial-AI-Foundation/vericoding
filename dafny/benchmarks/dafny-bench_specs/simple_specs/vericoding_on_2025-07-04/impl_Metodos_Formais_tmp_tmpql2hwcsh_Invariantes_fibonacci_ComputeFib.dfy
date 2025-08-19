//ATOM
// Provando fibonacci
function Fib(n:nat):nat
{
  if n < 2
  then n
  else Fib(n-2) + Fib(n-1)
}

//IMPL ComputeFib
method ComputeFib(n:nat) returns (x:nat)
ensures x == Fib(n)
{
  if n < 2 {
    x := n;
  } else {
    var a := 0;
    var b := 1;
    var i := 2;
    
    while i <= n
      invariant 2 <= i <= n + 1
      invariant a == Fib(i - 2)
      invariant b == Fib(i - 1)
    {
      var temp := a + b;
      a := b;
      b := temp;
      i := i + 1;
    }
    
    x := b;
  }
}