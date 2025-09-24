// <vc-preamble>
function fib(n : nat) : nat
{
  if (n==0) then 1 else
  if (n==1) then 1 else fib(n-1)+fib(n-2)
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Fib(n : nat) returns (r:nat)
  ensures r == fib(n)
// </vc-spec>
// <vc-code>
{
  if (n == 0) {
    return 1;
  }

  var next:= 2;
  r:=1;
  var i := 1;

  while (i < n)
    invariant next == fib(i+1)
    invariant r == fib(i)
    invariant 1 <= i <= n
  {
    var tmp := next;
    next := next + r;
    r := tmp;
    i := i + 1;
  }
  assert r == fib(n);
  return r;
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