

// <vc-helpers>
// Empty
// </vc-helpers>

// <vc-spec>
method IsPerfectSquare(n: int) returns (result: bool)
    requires n >= 0
    ensures result == true ==> (exists i: int :: 0 <= i <= n && i * i == n)
    ensures result == false ==> (forall a: int :: 0 < a*a < n ==> a*a != n)
// </vc-spec>
// <vc-code>
{
  result := false;
  var i := 0;
  while (i * i < n)
    invariant i >= 0
  {
    i := i + 1;
  }
  if (i * i == n) {
    result := true;
  }
}
// </vc-code>

