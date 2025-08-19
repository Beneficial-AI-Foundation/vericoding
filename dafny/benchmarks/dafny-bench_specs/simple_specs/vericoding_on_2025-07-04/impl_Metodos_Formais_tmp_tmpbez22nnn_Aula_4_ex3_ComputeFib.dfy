//ATOM
function Fib(n:nat):nat
{
  if n < 2
  then n
  else Fib(n-2) + Fib(n-1)
}

//IMPL 
method ComputeFib(n:nat) returns (x:nat)
ensures x == Fib(n)
{
  if n < 2 {
    x := n;
  } else {
    var a := 0;
    var b := 1;
    var i := 2;
    
    /* code modified by LLM (iteration 1): Fixed loop invariants to properly track Fibonacci values and ensure verification */
    while i <= n
      invariant 2 <= i <= n + 1
      invariant a == Fib(i-2)
      invariant b == Fib(i-1)
    {
      /* code modified by LLM (iteration 1): Added assertion to help Dafny verify the Fibonacci recurrence relation */
      assert Fib(i) == Fib(i-2) + Fib(i-1);
      var temp := a + b;
      a := b;
      b := temp;
      i := i + 1;
    }
    /* code modified by LLM (iteration 1): Added assertion to establish that b equals Fib(n) when loop exits */
    assert i == n + 1;
    assert b == Fib(n);
    x := b;
  }
}