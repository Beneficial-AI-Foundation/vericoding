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
lemma SocksAfterDayMonotonic(n: int, m: int, day1: int, day2: int)
  requires m >= 2
  requires day1 <= day2
  ensures SocksAfterDay(n, m, day1) >= SocksAfterDay(n, m, day2)
{
  // SocksAfterDay(n, m, day1) = n + day1 / m - day1
  // SocksAfterDay(n, m, day2) = n + day2 / m - day2
  // We need to show: n + day1 / m - day1 >= n + day2 / m - day2
  // Which simplifies to: day1 / m - day1 >= day2 / m - day2
  // Or: day2 - day1 >= day2 / m - day1 / m
  
  assert day1 / m <= day2 / m;
  assert day2 / m - day1 / m >= 0;
  
  // The key insight: day2/m - day1/m counts how many complete intervals of m
  // are between day1 and day2, which is at most (day2-day1)/m
  assert day2 / m - day1 / m <= (day2 - day1) / m;
  assert (day2 - day1) / m <= day2 - day1;
  assert day2 / m - day1 / m <= day2 - day1;
}

lemma SocksAfterDayBound(n: int, m: int, day: int)
  requires m >= 2
  requires day >= 1
  ensures SocksAfterDay(n, m, day) <= n + day / m - day
  ensures SocksAfterDay(n, m, day) >= n - day
{
}

lemma EventuallyRunOut(n: int, m: int)
  requires ValidInput(n, m)
  ensures exists day :: day > 0 && SocksAfterDay(n, m, day) <= 0
{
  var day := n * m + 1;
  assert day / m <= n;
  var socksAfterDay := SocksAfterDay(n, m, day);
  var upperBound := n + n - (n * m + 1);
  var simplifiedBound := 2 * n - n * m - 1;
  assert socksAfterDay <= upperBound;
  assert upperBound == simplifiedBound;
  assert simplifiedBound <= 0 by {
    assert n * m >= 2 * n;
  }
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
  result := n;
  
  while SocksAfterDay(n, m, result) > 0
    invariant result >= n
    invariant result > 0
    invariant forall k :: 1 <= k < result ==> SocksAfterDay(n, m, k) > 0
    decreases n * m + n - result
  {
    SocksAfterDayMonotonic(n, m, result, result + 1);
    result := result + 1;
  }
}
// </vc-code>

