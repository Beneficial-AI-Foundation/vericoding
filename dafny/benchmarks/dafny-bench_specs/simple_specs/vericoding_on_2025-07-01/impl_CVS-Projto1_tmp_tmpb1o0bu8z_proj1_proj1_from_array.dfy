//ATOM

///Exercicio 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

//ATOM

function mem<T(==)> (x: T, l:List<T>) : bool
{
  match l
  case Nil => false
  case Cons(y,r)=> if (x==y) then true else mem(x,r)
}


// SPEC

method from_array<T>(a: array<T>) returns (l: List<T>)
requires a.Length > 0
ensures forall j::0 <= j < a.Length ==> mem(a[j],l)
{
}