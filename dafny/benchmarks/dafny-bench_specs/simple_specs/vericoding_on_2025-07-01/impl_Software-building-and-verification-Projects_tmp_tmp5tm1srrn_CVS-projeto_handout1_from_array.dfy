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


// SPEC

method from_array<T>(a: array<T>) returns (l: List<T>)
 ensures forall i: int :: 0 <= i < a.Length ==> mem(a[i], l)
 ensures forall x: T :: mem(x, l) ==> exists y: int :: 0 <= y < a.Length && a[y] == x
{
}