// <vc-preamble>
ghost predicate IsPerfectSquare(n: nat)
{
    exists i: nat :: i * i == n
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsPerfectSquareFn(n: int) returns (result: bool)
    requires n >= 0
    ensures result <==> IsPerfectSquare(n as nat)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i * i < n
    invariant 0 <= i
    invariant forall j :: 0 <= j < i ==> j * j < n
  {
    i := i + 1;
  }
  result := i * i == n;
  if result {
    assert i * i == n;
    assert IsPerfectSquare(n);
  } else {
    assert i * i > n;
    assert forall j :: 0 <= j < i ==> j * j < n;
    forall j | 0 <= j
      ensures j * j != n
    {
      if j < i {
        assert j * j < n;
      } else if j == i {
        assert j * j > n;
      } else {
        assert j > i;
        assert j * j > i * i;
        assert i * i > n;
        assert j * j > n;
      }
    }
    assert !IsPerfectSquare(n);
  }
}
// </vc-code>
