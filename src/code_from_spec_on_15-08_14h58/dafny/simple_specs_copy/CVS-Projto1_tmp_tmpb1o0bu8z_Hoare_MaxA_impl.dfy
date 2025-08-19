//ATOM


datatype List<T> = Nil | Cons(head: T, tail: List<T>)


//IMPL 


method MaxA (a: array<int>) returns (m: int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures exists i :: 0 <= i < a.Length && a[i] == m
{
  m := a[0];
  var j := 1;
  
  while j < a.Length
    invariant 1 <= j <= a.Length
    invariant forall k :: 0 <= k < j ==> a[k] <= m
    invariant exists k :: 0 <= k < j && a[k] == m
  {
    if a[j] > m {
      m := a[j];
    }
    j := j + 1;
  }
}