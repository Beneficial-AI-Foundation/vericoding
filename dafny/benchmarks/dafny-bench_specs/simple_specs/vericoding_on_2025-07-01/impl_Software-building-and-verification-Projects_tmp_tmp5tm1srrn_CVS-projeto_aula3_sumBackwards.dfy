//ATOM

// 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

//ATOM

// 6
function sum(n: nat) : nat
{
 if (n == 0) then 0 else n + sum(n-1)
}


// SPEC

method sumBackwards(n: nat) returns (r: nat)
 ensures r == sum(n)
{
}