// <vc-spec>
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

// <vc-helpers>
// </vc-helpers>

method addImp(l : List<int>) returns (r: int)
  ensures r == add(l)
// </vc-spec>
// <vc-code>
{
  r := 0;
  var current := l;
  
  while current != Nil
    invariant r + add(current) == add(l)
    decreases current
  {
    match current {
      case Cons(head, tail) =>
        r := r + head;
        current := tail;
    }
  }
}
// </vc-code>

// 3.

// 5.

// 6
function sum(n: nat) : nat
{
  if (n == 0) then 0 else n + sum(n-1)
}