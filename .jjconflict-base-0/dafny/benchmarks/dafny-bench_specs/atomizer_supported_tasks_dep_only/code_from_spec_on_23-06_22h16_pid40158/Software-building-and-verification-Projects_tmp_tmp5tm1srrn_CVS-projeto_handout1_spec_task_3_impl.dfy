// 1 a)

// [ai, aj[
//ATOM sum

// 1 b)
//ATOM query

// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]
//ATOM queryFast

//ATOM is_prefix_sum_for

//ATOM proof

//ATOM List
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

//IMPL from_array
method from_array<T>(a: array<T>) returns (l: List<T>)
  ensures forall i: int :: 0 <= i < a.Length ==> mem(a[i], l)
  ensures forall x: T :: mem(x, l) ==> exists y: int :: 0 <= y < a.Length && a[y] == x
{
  l := Nil;
  var i := a.Length;
  while i > 0
    invariant 0 <= i <= a.Length
    invariant forall j: int :: i <= j < a.Length ==> mem(a[j], l)
    invariant forall x: T :: mem(x, l) ==> exists y: int :: i <= y < a.Length && a[y] == x
  {
    i := i - 1;
    l := Cons(a[i], l);
  }
}

// ATOM mem
function mem<T(==)> (x: T, l: List<T>) : bool
{
  match l
  case Nil => false
  case Cons(h, t) => h == x || mem(x, t)
}