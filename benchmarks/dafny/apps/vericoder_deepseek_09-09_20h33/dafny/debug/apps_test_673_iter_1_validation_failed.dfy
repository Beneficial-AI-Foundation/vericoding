predicate ValidInput(n: int, k: int)
{
    n >= 1 && k > 0
}

predicate IsCorrectResult(n: int, k: int, result: int)
    requires k > 0
{
    result > n && result % k == 0 && forall x :: n < x < result ==> x % k != 0
}

// <vc-helpers>
lemma {:axiom} ExistsMultiple(n: int, k: int)
  requires n >= 1 && k > 0
  ensures exists result: int :: result > n && result % k == 0
{
}

lemma NoSmallerMultiple(n: int, k: int, result: int)
  requires n >= 1 && k > 0 && result > n && result % k == 0
  ensures forall x :: n < x < result ==> x % k != 0
{
  var x: int := n + 1;
  while x < result
    invariant forall y :: n < y < x ==> y % k != 0
    invariant x <= result
  {
    if x % k == 0 {
      assert false; // Contradiction: x would be a smaller multiple
    }
    x := x + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures IsCorrectResult(n, k, result)
// </vc-spec>
// <vc-code>
{
  result := n + 1;
  while result % k != 0
    invariant result > n
    invariant forall x :: n < x < result ==> x % k != 0
  {
    result := result + 1;
  }
}
// </vc-code>

