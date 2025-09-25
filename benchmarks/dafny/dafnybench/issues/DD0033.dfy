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
method MaxA (a: array<int>) returns (m: int)
    requires a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
    ensures exists i :: 0 <= i < a.Length && a[i] == m
// </vc-spec>
// <vc-code>
{
    m := a[0];
    var i := 1;
    while i< a.Length
        invariant 1 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> a[j] <=m
        invariant exists j :: 0 <= j < i && a[j] ==m
    {
        if a[i] > m {
            m:= a[i];
        }
        i := i +1;
    }
}
// </vc-code>
