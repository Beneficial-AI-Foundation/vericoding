//ATOM

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

//ATOM

function fib (n: nat) : nat
{
  if n == 0 then 1 else
  if n == 1 then 1 else
  fib(n -1) + fib (n-2)
}

//IMPL 

method Fib (n: nat) returns (r:nat)
  ensures r == fib(n)
{
  if n == 0 {
    r := 1;
  } else if n == 1 {
    r := 1;
  } else {
    var a := 1;  // fib(0)
    var b := 1;  // fib(1)
    var i := 2;
    
    while i <= n
      invariant 2 <= i <= n + 1
      invariant a == fib(i - 2)
      invariant b == fib(i - 1)
    {
      var temp := a + b;
      a := b;
      b := temp;
      i := i + 1;
    }
    
    r := b;
  }
}