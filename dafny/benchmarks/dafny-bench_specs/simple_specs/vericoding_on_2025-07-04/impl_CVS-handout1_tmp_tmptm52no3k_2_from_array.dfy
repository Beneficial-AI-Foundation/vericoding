//ATOM

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

//ATOM

function length<T>(l: List<T>): nat
{
 match l
 case Nil => 0
 case Cons(_, t) => 1 + length(t)
}

//ATOM

predicate mem<T(==)> (l: List<T>, x: T)
{
 match l
 case Nil => false
 case Cons(h, t) => if(h == x) then true else mem(t, x)
}

//ATOM

function at<T>(l: List<T>, i: nat): T
 requires i < length(l)
{
 if i == 0 then l.head else at(l.tail, i - 1)
}

//IMPL 

method from_array<T>(a: array<T>) returns (l: List<T>)
 requires a.Length >= 0
 ensures length(l) == a.Length
 ensures forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[i]
 ensures forall x :: mem(l, x) ==> exists i: int :: 0 <= i < length(l) && a[i] == x
{
    l := Nil;
    var j := a.Length;
    
    /* code modified by LLM (iteration 2): Fixed loop invariants to correctly model that when building list in reverse, at(l, i) corresponds to a[a.Length - 1 - i], and simplified membership invariants */
    while j > 0
        invariant 0 <= j <= a.Length
        invariant length(l) == a.Length - j
        invariant forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[a.Length - 1 - i]
        invariant forall x :: mem(l, x) ==> exists k: int :: j <= k < a.Length && a[k] == x
        invariant forall k: int :: j <= k < a.Length ==> mem(l, a[k])
    {
        j := j - 1;
        l := Cons(a[j], l);
    }
}