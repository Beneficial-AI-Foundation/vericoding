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

// IMPL

method from_array<T>(a: array<T>) returns (l: List<T>)
 requires a.Length >= 0
 ensures length(l) == a.Length
 ensures forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[i]
 ensures forall x :: mem(l, x) ==> exists i: int :: 0 <= i < length(l) && a[i] == x
{
    l := Nil;
    var j := a.Length;
    
    while j > 0
        invariant 0 <= j <= a.Length
        invariant length(l) == a.Length - j
        /* code modified by LLM (iteration 2): Fixed invariant to correctly map list indices to array indices */
        invariant forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[j + i]
        /* code modified by LLM (iteration 2): Fixed membership invariant with bidirectional relationship */
        invariant forall x :: mem(l, x) <==> exists i: int :: j <= i < a.Length && a[i] == x
    {
        j := j - 1;
        l := Cons(a[j], l);
    }
}