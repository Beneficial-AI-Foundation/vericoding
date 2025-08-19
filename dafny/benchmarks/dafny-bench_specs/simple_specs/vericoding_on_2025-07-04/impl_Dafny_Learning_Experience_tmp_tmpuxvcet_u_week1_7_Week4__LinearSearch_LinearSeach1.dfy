//ATOM

predicate P(n: int) {
  n % 2 == 0
}


//IMPL 

method LinearSeach1<T>(a: array<T>, P: T -> bool) returns (n: int)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || P(a[n])
  ensures n == a.Length ==> forall i :: 0 <= i < a.Length ==> !P(a[i])
{
  n := 0;
  while n < a.Length
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> !P(a[i])
  {
    if P(a[n]) {
      return;
    }
    n := n + 1;
  }
}