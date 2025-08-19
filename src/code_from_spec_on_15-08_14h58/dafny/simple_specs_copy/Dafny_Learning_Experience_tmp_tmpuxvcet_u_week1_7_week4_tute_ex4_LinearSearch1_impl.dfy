// IMPL

method LinearSearch1<T>(a: array<T>, P: T -> bool, s1:seq<T>) returns (n: int)
  requires |s1| <= a.Length
  requires forall i:: 0<= i <|s1| ==> s1[i] == a[i]
  ensures -1 <= n < a.Length
  ensures n == -1 || P(a[n])
  ensures n != -1 ==> forall i :: 0 <= i < n ==> ! P(a[i])
  ensures n == -1 ==> forall i :: 0 <= i < |s1| ==> ! P(a[i])
{
  n := 0;
  while n < |s1|
    invariant 0 <= n <= |s1|
    invariant forall i :: 0 <= i < n ==> !P(a[i])
  {
    if P(a[n]) {
      return;
    }
    n := n + 1;
  }
  n := -1;
}