//ATOM

// 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)


//ATOM

// 6
function sum(n: nat) : nat
{
 if (n == 0) then 0 else n + sum(n-1)
}


//IMPL 

method sumBackwards(n: nat) returns (r: nat)
 ensures r == sum(n)
{
    r := 0;
    var i := n;
    while i > 0
        invariant 0 <= i <= n
        invariant r == sum(n) - sum(i)
    {
        r := r + i;
        i := i - 1;
    }
}