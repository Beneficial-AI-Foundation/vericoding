// <vc-preamble>
function fib(n : nat) : nat
{
  if (n==0) then 1 else
  if (n==1) then 1 else fib(n-1)+fib(n-2)
}


// 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function add(l : List<int>) : int {
  match l
  case Nil => 0
  case Cons(x,xs) => x + add(xs)
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method addImp(l : List<int>) returns (r: int)
  ensures r == add(l)
// </vc-spec>
// <vc-code>
{
  r := 0;
  var ll := l;
  while (ll != Nil)
    decreases ll
    invariant r==add(l) - add(ll)
  {
    r := r + ll.head;
    ll := ll.tail;

  }

  assert r == add(l);
}
// </vc-code>

// 3.

// 5.

// 6
function sum(n: nat) : nat
{
  if (n == 0) then 0 else n + sum(n-1)
}