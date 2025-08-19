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


//IMPL 

//Exercicio 1.b)
method query (a:array<int>, i:int, j:int) returns (s:int)
requires 0 <= i <= j <= a.Length
ensures s == sum(a, i, j)
{
  s := sum(a, i, j);
}