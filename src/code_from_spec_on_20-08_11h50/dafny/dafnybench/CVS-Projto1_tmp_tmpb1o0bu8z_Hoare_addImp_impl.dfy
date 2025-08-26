// <vc-spec>
function fib (n: nat) : nat
{
    if n == 0 then 1 else
    if n == 1 then 1 else
    fib(n -1) + fib (n-2)
}



datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function add(l:List<int>) : int
{
    match l
    case Nil => 0
    case Cons(x, xs) => x + add(xs)
}

// <vc-helpers>
function length<T>(l: List<T>): nat
{
    match l
    case Nil => 0
    case Cons(_, tail) => 1 + length(tail)
}
// </vc-helpers>

method addImp (l: List<int>) returns (s: int)
    ensures s == add(l)
// </vc-spec>
// <vc-code>
{
  s := 0;
  var current := l;
  
  while current != Nil
    invariant s + add(current) == add(l)
    decreases length(current)
  {
    match current {
      case Cons(head, tail) =>
        s := s + head;
        current := tail;
    }
  }
}
// </vc-code>