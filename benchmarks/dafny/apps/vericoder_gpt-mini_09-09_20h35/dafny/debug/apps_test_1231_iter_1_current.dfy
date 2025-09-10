predicate ValidInput(a: int, b: int)
{
    0 <= a <= 100 && 0 <= b <= 100
}

predicate ValidOutput(result: string)
{
    result == "YES" || result == "NO"
}

predicate IntervalExists(a: int, b: int)
{
    abs(a - b) <= 1 && a + b > 0
}

function abs(x: int): int
{
    if x >= 0 then x else -x
}

// <vc-helpers>
// No additional helpers required.
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: string)
    requires ValidInput(a, b)
    ensures ValidOutput(result)
    ensures result == "YES" <==> IntervalExists(a, b)
// </vc-spec>
// <vc-code>
{
  var cond := abs(a - b) <= 1 && a + b > 0;
  if cond {
    result := "YES";
  } else {
    result := "NO";
  }
  // result corresponds to cond
  assert result == "YES" <==> cond;
  // unfold IntervalExists (definitionally equal to cond)
  assert cond <==> IntervalExists(a, b);
  assert result == "YES" <==> IntervalExists(a, b);
  // ensure ValidOutput
  assert result == "YES" || result == "NO";
}
// </vc-code>

