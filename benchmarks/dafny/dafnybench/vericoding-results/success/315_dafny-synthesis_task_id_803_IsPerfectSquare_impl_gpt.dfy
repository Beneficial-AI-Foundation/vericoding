

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsPerfectSquare(n: int) returns (result: bool)
    requires n >= 0
    ensures result == true ==> (exists i: int :: 0 <= i <= n && i * i == n)
    ensures result == false ==> (forall a: int :: 0 < a*a < n ==> a*a != n)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    decreases n - i + 1
  {
    if i * i == n {
      assert 0 <= i <= n;
      result := true;
      return;
    }
    i := i + 1;
  }
  result := false;
}
// </vc-code>

