//ATOM 
// 1 a)

// [ai, aj[
function sum(a: array<int>, i: int, j: int) : int
  requires 0 <= i <= j <= a.Length
  reads a
{
  if i == j then 0
  else a[j-1] + sum(a, i, j-1)
}


//IMPL query
// 1 b)
method query(a: array<int>, i: int, j: int) returns (res : int)
  requires 0 <= i <= j <= a.Length
  ensures res == sum(a, i, j)
{
  res := sum(a, i, j);
}


//IMPL queryFast
// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]
method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a,c)
  ensures r == sum(a, i, j)
{
  /* code modified by LLM (iteration 1): use proof lemma to establish prefix sum property */
  proof(a, 0, i, j);
  r := c[j] - c[i];
}


//ATOM 
predicate is_prefix_sum_for (a: array<int>, c: array<int>)
  reads c, a
{
  a.Length + 1 == c.Length && forall i: int :: 0 <= i <= a.Length ==> c[i] == sum(a, 0, i)
}


//ATOM 
lemma proof(a: array<int>, i: int, j: int, k:int)
  requires 0 <= i <= k <= j <= a.Length
  ensures sum(a, i, k) + sum(a, k, j) == sum(a, i, j)
{
}


//ATOM 
// 2
datatype List<T> = Nil | Cons(head: T, tail: List<T>)


//IMPL from_array
method from_array<T>(a: array<T>) returns (l: List<T>)
  ensures forall i: int :: 0 <= i < a.Length ==> mem(a[i], l)
  ensures forall x: T :: mem(x, l) ==> exists y: int :: 0 <= y < a.Length && a[y] == x
{
  l := Nil;
  var k := 0;
  while k < a.Length
    invariant 0 <= k <= a.Length
    invariant forall i: int :: 0 <= i < k ==> mem(a[i], l)
    invariant forall x: T :: mem(x, l) ==> exists y: int :: 0 <= y < k && a[y] == x
  {
    l := Cons(a[k], l);
    k := k + 1;
  }
}


//ATOM 
function mem<T(==)> (x: T, l: List<T>) : bool
{
  match l
  case Nil => false
  case Cons(h, t) => h == x || mem(x, t)
}