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

//IMPL from_array

method from_array<T>(a: array<T>) returns (l: List<T>)
 requires a.Length >= 0
 ensures length(l) == a.Length
 ensures forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[i]
 ensures forall x :: mem(l, x) ==> exists i: int :: 0 <= i < length(l) && a[i] == x
{
    l := Nil;
    
    /* code modified by LLM (iteration 1): Changed to reverse iteration to build list correctly */
    var k := a.Length;
    
    while k > 0
        invariant 0 <= k <= a.Length
        invariant length(l) == a.Length - k
        invariant forall i: int :: k <= i < a.Length ==> at(l, i - k) == a[i]
        invariant forall x :: mem(l, x) ==> exists i: int :: k <= i < a.Length && a[i] == x
        decreases k
    {
        k := k - 1;
        /* code modified by LLM (iteration 1): Prepend element to maintain correct ordering */
        l := Cons(a[k], l);
    }
}