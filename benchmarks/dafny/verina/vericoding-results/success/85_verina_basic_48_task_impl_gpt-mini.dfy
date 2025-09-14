// <vc-preamble>
ghost predicate IsPerfectSquare(n: nat)
{
    exists i: nat :: i * i == n
}
// </vc-preamble>

// <vc-helpers>
lemma FoundImpliesIsPerfectSquare(i: nat, n: nat)
  requires i * i == n
  ensures IsPerfectSquare(n)
{
}

lemma SquareMonotone(a: nat, b: nat)
  requires a <= b
  ensures a * a <= b * b
{
}
// </vc-helpers>

// <vc-spec>
method IsPerfectSquareFn(n: int) returns (result: bool)
    requires n >= 0
    ensures result <==> IsPerfectSquare(n as nat)
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  while i * i <= n
    invariant 0 <= i <= n + 1
    invariant forall j: nat :: j < i ==> j * j != n
    decreases n - i
  {
    if i * i == n {
      result := true;
      return;
    }
    i := i + 1;
  }
  result := false;
}
// </vc-code>
