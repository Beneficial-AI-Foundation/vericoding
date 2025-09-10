predicate ValidInput(n: int, m: int) {
    n >= 1 && m >= 2
}

function SocksAfterDay(n: int, m: int, day: int): int
  requires m > 0
{
    n + day / m - day
}

predicate CanWearSocksOnDay(n: int, m: int, day: int) 
  requires m > 0
{
    day >= 1 ==> SocksAfterDay(n, m, day - 1) > 0
}

// <vc-helpers>
lemma DivNonNeg(x: int, y: int)
  requires x >= 0 && y > 0
  ensures x / y >= 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures result >= n
  ensures result > 0
  ensures SocksAfterDay(n, m, result) <= 0
  ensures forall k :: 1 <= k < result ==> SocksAfterDay(n, m, k) > 0
// </vc-spec>
// <vc-code>
{
  var day := 1;
  while SocksAfterDay(n, m, day) > 0
    invariant day >= 1
    invariant m > 0
    invariant forall k :: 1 <= k < day ==> SocksAfterDay(n, m, k) > 0
    decreases SocksAfterDay(n, m, day), day % m
  {
    day := day + 1;
  }
  result := day;

  assert SocksAfterDay(n, m, result) <= 0;

  assert n + result / m - result <= 0;
  assert result - result / m >= n;

  assert result >= 1;
  assert m > 0;
  DivNonNeg(result, m);
  assert result / m >= 0;
  assert result >= result - result / m;

  assert result >= n;
  assert result > 0;
}
// </vc-code>

