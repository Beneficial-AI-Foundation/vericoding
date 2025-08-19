// IMPL
method IsPerfectSquare(n: int) returns (result: bool)
  requires n >= 0
  ensures result == true ==> (exists i: int :: 0 <= i <= n && i * i == n)
  ensures result == false ==> (forall a: int :: 0 < a*a < n ==> a*a != n)
{
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant forall j: int :: 0 <= j < i ==> j * j != n
  {
    if i * i == n {
      result := true;
      return;
    }
    if i * i > n {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := false;
}