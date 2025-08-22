//ATOM

predicate P(n: int) {
  n % 2 == 0
}


// SPEC
method LinearSeach0<T>(a: array<T>, P: T -> bool) returns (n: int)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || P(a[n])
{
}
