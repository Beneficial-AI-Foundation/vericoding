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
  var i: nat := 0;
  while i * i < n
    invariant forall k: nat :: k < i ==> k * k != n
  {
    i := i + 1;
  }
  result := i * i == n;
}
// </vc-code>
