// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method addImp (l: List<int>) returns (s: int)
    ensures s == add(l)
// </vc-spec>
// <vc-code>
{
    var ll := l;
    s := 0;
    while ll != Nil
        decreases ll
        invariant add(l) == s + add(ll)
        {
            s := s + ll.head;
            ll:= ll.tail;
        }
    assert s == add(l);
}
// </vc-code>
