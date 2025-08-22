// 1 a)

// [ai, aj[
//ATOM_PLACEHOLDER_sum

// 1 b)
//ATOM_PLACEHOLDER_query

// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]
//ATOM_PLACEHOLDER_queryFast

//ATOM_PLACEHOLDER_is_prefix_sum_for

//ATOM_PLACEHOLDER_proof//ATOM_PLACEHOLDER_List// SPEC 

method from_array<T>(a: array<T>) returns (l: List<T>)
  ensures forall i: int :: 0 <= i < a.Length ==> mem(a[i], l)
  ensures forall x: T :: mem(x, l) ==> exists y: int :: 0 <= y < a.Length && a[y] == x
{
}


// ATOM 

function mem<T(==)> (x: T, l: List<T>) : bool
{
  match l
  case Nil => false
  case Cons(h, t) => h == x || mem(x, t)
}


