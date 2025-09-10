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
lemma SocksDecreaseDaily(n: int, m: int, day: int)
  requires m >= 2
  requires day >= 0
  ensures SocksAfterDay(n, m, day + 1) == SocksAfterDay(n, m, day) - 1 + (if (day + 1) % m == 0 then 1 else 0)
{
  if (day + 1) % m == 0 {
    assert (day + 1) / m == day / m + 1;
  } else {
    assert (day + 1) / m == day / m;
  }
}

lemma ResultBounds(n: int, m: int, result: int)
  requires n >= 1 && m >= 2
  requires result == n * m / (m - 1)
  ensures result >= n
  ensures result > 0
{
  assert m - 1 >= 1;
  assert n * m >= n * (m - 1);
  assert n * m / (m - 1) >= n;
}

lemma SocksRunOut(n: int, m: int, result: int)
  requires n >= 1 && m >= 2
  requires result == n * m / (m - 1)
  ensures SocksAfterDay(n, m, result) <= 0
{
  var socks := n + result / m - result;
  assert result * (m - 1) >= n * m;
  assert result - result / m >= n * m / (m - 1) - n * m / (m - 1) / m;
  assert result - result / m >= n;
  assert socks <= 0;
}

lemma SocksPositiveBefore(n: int, m: int, result: int, k: int)
  requires n >= 1 && m >= 2
  requires result == n * m / (m - 1)
  requires 1 <= k < result
  ensures SocksAfterDay(n, m, k) > 0
{
  var socks := n + k / m - k;
  assert k < n * m / (m - 1);
  assert k * (m - 1) < n * m;
  assert k - k / m < n;
  assert socks > 0;
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
  result := n * m / (m - 1);
  
  ResultBounds(n, m, result);
  SocksRunOut(n, m, result);
  
  forall k | 1 <= k < result
    ensures SocksAfterDay(n, m, k) > 0
  {
    SocksPositiveBefore(n, m, result, k);
  }
}
// </vc-code>

