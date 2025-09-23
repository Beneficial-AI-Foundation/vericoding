// <vc-preamble>
function fib (n: nat) : nat
{
    if n == 0 then 1 else
    if n == 1 then 1 else
    fib(n -1) + fib (n-2)
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Fib (n: nat) returns (r:nat)
    ensures r == fib(n)
// </vc-spec>
// <vc-code>
{
    if (n == 0) {
        return 1;
    }
    r := 1;
    var next:=2;
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant r == fib(i)
        invariant next == fib(i+1)
    {
        var tmp:=next;
        next:= next + r;
        r:= tmp;
        i:= i + 1;
    }
    assert r == fib(n);
    return r;
}
// </vc-code>

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function add(l:List<int>) : int
{
    match l
    case Nil => 0
    case Cons(x, xs) => x + add(xs)
}