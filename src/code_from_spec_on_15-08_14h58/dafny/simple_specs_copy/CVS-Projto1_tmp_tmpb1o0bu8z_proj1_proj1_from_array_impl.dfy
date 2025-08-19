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


//IMPL 

method from_array<T>(a: array<T>) returns (l: List<T>)
requires a.Length > 0
ensures forall j::0 <= j < a.Length ==> mem(a[j],l)
{
  l := Nil;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> mem(a[k], l)
  {
    l := Cons(a[i], l);
    i := i + 1;
  }
}