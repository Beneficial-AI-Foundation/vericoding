//ATOM


// 2

datatype List<T> = Nil | Cons(head: T, tail: List<T>)


//ATOM

function mem<T(==)> (x: T, l: List<T>) : bool
{
 match l
 case Nil => false
 case Cons(h, t) => h == x || mem(x, t)
}


//IMPL from_array

method from_array<T>(a: array<T>) returns (l: List<T>)
 ensures forall i: int :: 0 <= i < a.Length ==> mem(a[i], l)
 ensures forall x: T :: mem(x, l) ==> exists y: int :: 0 <= y < a.Length && a[y] == x
{
    l := Nil;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j: int :: 0 <= j < i ==> mem(a[j], l)
        invariant forall x: T :: mem(x, l) ==> exists y: int :: 0 <= y < i && a[y] == x
    {
        l := Cons(a[i], l);
        i := i + 1;
    }
}