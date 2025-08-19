//ATOM

datatype List<T> = Nil | Cons(head: T, tail: List<T>)


// SPEC


method MaxA (a: array<int>) returns (m: int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures exists i :: 0 <= i < a.Length && a[i] == m
{
}