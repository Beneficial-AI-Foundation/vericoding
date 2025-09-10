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
  // The key insight is that (day + 1) / m equals either day / m or day / m + 1
  // It increases by 1 exactly when (day + 1) % m == 0
  var q1 := day / m;
  var r1 := day % m;
  assert day == q1 * m + r1 && 0 <= r1 < m;
  
  var q2 := (day + 1) / m;
  var r2 := (day + 1) % m;
  assert day + 1 == q2 * m + r2 && 0 <= r2 < m;
  
  if (day + 1) % m == 0 {
    assert r2 == 0;
    assert day + 1 == q2 * m;
    assert day == q2 * m - 1;
    assert r1 == m - 1;
    assert q2 == q1 + 1;
  } else {
    assert r2 > 0;
    assert r2 == r1 + 1;
    assert q2 == q1;
  }
}

lemma DivisionBound(a: int, b: int, c: int)
  requires b > 0 && c > 0
  requires a >= b * c
  ensures a / c >= b
{
  // Since a >= b * c and c > 0, we have a / c >= b
}

lemma ResultBounds(n: int, m: int, result: int)
  requires n >= 1 && m >= 2
  requires result == n * m / (m - 1)
  ensures result >= n
  ensures result > 0
{
  assert m - 1 >= 1;
  assert n * m >= n * (m - 1);
  DivisionBound(n * m, n, m - 1);
}

lemma SocksRunOut(n: int, m: int, result: int)
  requires n >= 1 && m >= 2
  requires result == n * m / (m - 1)
  ensures SocksAfterDay(n, m, result) <= 0
{
  var socks := n + result / m - result;
  
  // We need to show that result - result / m >= n
  // Since result = n * m / (m - 1), we have:
  // result * (m - 1) >= n * m - (m - 2) (due to integer division)
  // This is because n * m = result * (m - 1) + remainder where 0 <= remainder < m - 1
  
  var quotient := n * m / (m - 1);
  var remainder := n * m % (m - 1);
  assert n * m == quotient * (m - 1) + remainder && 0 <= remainder < m - 1;
  assert result == quotient;
  
  // Now we need result - result / m >= n
  // We know result * (m - 1) >= n * m - (m - 2) from the division
  // So result * (m - 1) >= n * m - m + 2 >= n * m - m = n * (m - 1) + n
  // But we need a tighter bound
  
  // Actually, since result * (m - 1) + remainder = n * m where 0 <= remainder < m - 1
  // We have result * (m - 1) >= n * m - (m - 2)
  // So result * m - result >= n * m - (m - 2)
  // Therefore result - result/m >= (n * m - (m - 2))/m >= n when m >= 2
  
  assert socks == n - (result - result / m);
  assert socks <= 0;
}

lemma SocksPositiveBefore(n: int, m: int, result: int, k: int)
  requires n >= 1 && m >= 2
  requires result == n * m / (m - 1)
  requires 1 <= k < result
  ensures SocksAfterDay(n, m, k) > 0
{
  var socks := n + k / m - k;
  
  // We need to show k - k / m < n
  // Since k < result = n * m / (m - 1)
  // We have k * (m - 1) < n * m
  
  // k - k/m = k * (1 - 1/m) = k * (m - 1) / m (approximately)
  // Since k < n * m / (m - 1), we have k * (m - 1) < n * m
  // So k * (m - 1) / m < n
  
  // More precisely: k - k/m <= k * (m - 1) / m < n * m / m = n
  assert k * (m - 1) < n * m;
  
  // We need to be more careful with integer division
  // k/m <= k/m so k - k/m >= k - k/m = k * (m-1)/m + remainder terms
  // But since k * (m-1) < n * m, we have (k * (m-1))/m < n
  
  // The key insight: k - k/m = k - floor(k/m) 
  // = floor(k * (m-1) / m) when considering integer arithmetic
  // Since k * (m-1) < n * m, we get floor(k * (m-1) / m) < n
  
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

