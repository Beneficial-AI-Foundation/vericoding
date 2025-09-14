// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma SquareStrictlyMonotonic(a: nat, b: nat)
  requires a < b
  ensures a*a < b*b
{}
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
    while i * i <= n
      invariant 0 <= i
      invariant forall k: int :: 0 <= k < i ==> k * k != n
      decreases n - i * i
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
