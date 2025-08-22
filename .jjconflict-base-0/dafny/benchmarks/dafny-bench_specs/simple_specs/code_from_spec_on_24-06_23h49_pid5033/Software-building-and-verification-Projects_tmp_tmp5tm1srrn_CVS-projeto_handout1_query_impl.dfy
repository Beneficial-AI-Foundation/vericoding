//ATOM


// 2

datatype List<T> = Nil | Cons(head: T, tail: List<T>)


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
 if i == j {
  res := 0;
 } else {
  var subres := query(a, i, j-1);
  res := a[j-1] + subres;
 }
}