//IMPL 
method LinearSearch<T>(a: array<T>, P: T -> bool) returns (n: int)
  ensures -1 <= n < a.Length
  ensures n == -1 || P(a[n])
  ensures n != -1 ==> forall i :: 0 <= i < n ==> ! P(a[i])
  ensures n == -1 ==> forall i :: 0 <= i < a.Length ==> ! P(a[i])
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> !P(a[j])
  {
    if P(a[i]) {
      return i;
    }
    i := i + 1;
  }
  return -1;
}