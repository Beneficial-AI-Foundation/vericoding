// SPEC
method LinearSearch<T>(a: array<T>, P: T -> bool) returns (n: int)
  ensures -1 <= n < a.Length
  ensures n == -1 || P(a[n])
  ensures n != -1 ==> forall i :: 0 <= i < n ==> ! P(a[i])
  ensures n == -1 ==> forall i :: 0 <= i < a.Length ==> ! P(a[i])
{
}
