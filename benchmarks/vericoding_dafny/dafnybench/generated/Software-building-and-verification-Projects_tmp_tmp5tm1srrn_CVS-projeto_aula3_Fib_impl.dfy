// The recursive `fib` function is inefficient for large `n`, so I'll implement an iterative version that computes Fibonacci numbers in linear time using two variables to track the last two Fibonacci values.

// <vc-spec>
function fib(n : nat) : nat
{
  if (n==0) then 1 else
  if (n==1) then 1 else fib(n-1)+fib(n-2)
}

// <vc-helpers>
// </vc-helpers>

method Fib(n : nat) returns (r:nat)
  ensures r == fib(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 || n == 1 {
    r := 1;
  } else {
    var prev := 1;  // fib(0);
    var curr := 1;  // fib(1);
    var i := 2;
    
    while i <= n
      invariant 2 <= i <= n + 1
      invariant prev == fib(i-2)
      invariant curr == fib(i-1)
    {
      var next := prev + curr;
      prev := curr;
      curr := next;
      i := i + 1;
    }
    
    r := curr;
  }
}
// </vc-code>

// 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function add(l : List<int>) : int {
  match l
  case Nil => 0
  case Cons(x,xs) => x + add(xs)
}


// 3.

// 5.

// 6
function sum(n: nat) : nat
{
  if (n == 0) then 0 else n + sum(n-1)
}