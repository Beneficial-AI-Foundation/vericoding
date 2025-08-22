// SPEC 
method Max (x: nat, y:nat) returns (r:nat)
    ensures (r >= x && r >=y)
    ensures (r == x || r == y)
{
}


// SPEC 

method Test ()
{
}


// SPEC 

method m1 (x: int, y: int) returns (z: int)
requires 0 < x < y
ensures z >= 0 && z <= y && z != x
{
}




// ATOM 



function fib (n: nat) : nat
{
    if n == 0 then 1 else
    if n == 1 then 1 else
    fib(n -1) + fib (n-2)
}


// SPEC 

method Fib (n: nat) returns (r:nat)
    ensures r == fib(n)
{
}



// ATOM 


datatype List<T> = Nil | Cons(head: T, tail: List<T>)
// ATOM 

function add(l:List<int>) : int
{
    match l
    case Nil => 0
    case Cons(x, xs) => x + add(xs)
}



// SPEC 


method addImp (l: List<int>) returns (s: int)
    ensures s == add(l)
{
}



// SPEC 


method MaxA (a: array<int>) returns (m: int)
    requires a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
    ensures exists i :: 0 <= i < a.Length && a[i] == m
{
}




