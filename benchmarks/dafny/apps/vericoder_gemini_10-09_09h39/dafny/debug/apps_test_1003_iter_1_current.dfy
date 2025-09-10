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
lemma LemmaSocksPositiveForEarlyDays(n: int, m: int)
  requires ValidInput(n, m)
  ensures forall k :: 1 <= k < n ==> SocksAfterDay(n, m, k) > 0
{
  forall k | 1 <= k < n
    ensures SocksAfterDay(n, m, k) > 0
  {
    assert k/m >= 0;
    assert SocksAfterDay(n, m, k) == n + k/m - k >= n - k;
    assert k < n ==> n - k >= 1;
    assert SocksAfterDay(n, m, k) > 0;
  }
}

lemma LemmaBoundOnResult(n: int, m: int)
  requires ValidInput(n, m)
  ensures SocksAfterDay(n, m, n * m) <= 0
{
  assert m > 0 by {
    assert m >= 2;
  }
  calc {
    SocksAfterDay(n, m, n * m);
    n + (n * m) / m - n * m;
    n + n - n * m;
    n * (2 - m);
  }
  assert n * (2 - m) <= 0;
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
  LemmaBoundOnResult(n, m);
// </vc-code>

