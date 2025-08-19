//ATOM

///Exercicio 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)


//ATOM
//Exercicio 1.a)
function sum (a:array<int>, i:int, j:int) :int
reads a
requires 0 <= i <= j <= a.Length
{
  if i == j then
    0
  else
    a[j-1] + sum(a, i, j-1)
}


//ATOM

predicate is_prefix_sum_for (a:array<int>, c:array<int>)
reads c, a
{
  a.Length + 1 == c.Length
  && c[0] == 0
  && forall j :: 1 <= j <= a.Length ==> c[j] == sum(a,0,j)
}


//IMPL

method queryFast (a:array<int>, c:array<int>, i:int, j:int) returns (r:int)
requires is_prefix_sum_for(a,c) && 0 <= i <= j <= a.Length < c.Length
ensures r == sum(a, i,j)
{
  r := c[j] - c[i];
}