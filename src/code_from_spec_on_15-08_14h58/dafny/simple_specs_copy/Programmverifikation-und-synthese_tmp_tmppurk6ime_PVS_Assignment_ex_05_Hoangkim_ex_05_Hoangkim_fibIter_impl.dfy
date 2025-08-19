//ATOM
function fib(n: nat):nat
{
  if n < 2 then n else fib(n-2)+fib(n-1)
}

//IMPL fibIter
method fibIter(n:nat) returns (a:nat)
requires n > 0
ensures a == fib(n)
{
  /* code modified by LLM (iteration 1): Fixed edge case handling for n=1 and n=2, added proper loop invariants */
  if n == 1 {
    a := 1;
  } else if n == 2 {
    a := 1;
  } else {
    var prev := 0;
    var curr := 1;
    var i := 2;
    
    while i <= n
      invariant 2 <= i <= n + 1
      invariant prev == fib(i - 2)
      invariant curr == fib(i - 1)
    {
      var temp := curr;
      curr := prev + curr;
      prev := temp;
      i := i + 1;
    }
    
    a := curr;
  }
}