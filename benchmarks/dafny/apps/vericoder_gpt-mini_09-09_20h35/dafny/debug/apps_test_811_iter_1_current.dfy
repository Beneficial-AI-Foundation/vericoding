predicate ValidInput(a: int, b: int)
{
  a >= 1 && a <= 1000 && b >= 2 && b <= 1000
}

function TotalBurningHours(a: int, b: int): int
  requires a >= 0 && b >= 2
  ensures TotalBurningHours(a, b) >= a
  decreases a
{
  if a == 0 then 0
  else if a < b then a
  else a + TotalBurningHours(a / b, b)
}

// <vc-helpers>
lemma TotalBurningHours_unroll(a: int, b: int)
  requires a >= b && a >= 0 && b >= 2
  ensures TotalBurningHours(a, b) == a + TotalBurningHours(a / b, b)
{
  // By the definition of TotalBurningHours, when a >= b the function unfolds to a + TotalBurningHours(a / b, b)
  assert TotalBurningHours(a, b) ==
         (if a == 0 then 0 else if a < b then a else a + TotalBurningHours(a / b, b));
  // Given the precondition a >= b, the conditional picks the third branch
  assert (if a == 0 then 0 else if a < b then a else a + TotalBurningHours(a / b, b))
         == a + TotalBurningHours(a / b, b);
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
  requires ValidInput(a, b)
  ensures result >= a
  ensures result == TotalBurningHours(a, b)
// </vc-spec>
// <vc-code>
{
  var cur := a;
  var acc := 0;
  var orig := a;
  while cur >= b
    invariant cur >= 0
    invariant acc >= 0
    invariant TotalBurningHours(orig, b) == acc + TotalBurningHours(cur, b)
    decreases cur
  {
    // unfold the function for the current value to preserve the invariant after the update
    assert cur > 0;
    TotalBurningHours_unroll(cur, b);
    acc := acc + cur;
    cur := cur / b;
  }
  result := acc + cur;
  assert result == TotalBurningHours(orig, b);
}
// </vc-code>

