// IMPL 
method Max (x: nat, y:nat) returns (r:nat)
    ensures (r >= x && r >=y)
    ensures (r == x || r == y)
{
    if x >= y {
        r := x;
    } else {
        r := y;
    }
}


// IMPL 
method Test ()
{
}


// IMPL 
method m1 (x: int, y: int) returns (z: int)
requires 0 < x < y
ensures z >= 0 && z <= y && z != x
{
    /* code modified by LLM (iteration 1): changed z := 0 to z := y to satisfy postcondition z != x */
    z := y;
}




// ATOM 
function fib (n: nat) : nat
{
    if n == 0 then 1 else
    if n == 1 then 1 else
    fib(n -1) + fib (n-2)
}


// IMPL 
method Fib (n: nat) returns (r:nat)
    ensures r == fib(n)
{
    if n == 0 {
        r := 1;
    } else if n == 1 {
        r := 1;
    } else {
        var a := 1;
        var b := 1;
        var i := 2;
        while i <= n
            invariant 2 <= i <= n + 1
            invariant a == fib(i - 2)
            invariant b == fib(i - 1)
        {
            var temp := a + b;
            a := b;
            b := temp;
            i := i + 1;
        }
        r := b;
    }
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



// IMPL 
method addImp (l: List<int>) returns (s: int)
    ensures s == add(l)
{
    s := 0;
    var current := l;
    while current != Nil
        invariant s + add(current) == add(l)
        /* code modified by LLM (iteration 1): added decreases clause for termination */
        decreases current
    {
        s := s + current.head;
        current := current.tail;
    }
}



// IMPL 
method MaxA (a: array<int>) returns (m: int)
    requires a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
    ensures exists i :: 0 <= i < a.Length && a[i] == m
{
    m := a[0];
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> a[j] <= m
        invariant exists j :: 0 <= j < i && a[j] == m
    {
        if a[i] > m {
            m := a[i];
        }
        i := i + 1;
    }
}