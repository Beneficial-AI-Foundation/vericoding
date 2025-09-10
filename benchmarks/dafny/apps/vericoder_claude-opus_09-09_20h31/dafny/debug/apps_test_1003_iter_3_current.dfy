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
lemma DivisionBound(a: int, b: int, c: int)
  requires b > 0 && c > 0
  requires a >= b * c
  ensures a / c >= b
{
  // Since a >= b * c and c > 0, we have a / c >= (b * c) / c = b
  assert a >= b * c;
  assert (b * c) / c == b;
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
  assert result >= n;
  assert result >= 1;
}

lemma SocksRunOut(n: int, m: int, result: int)
  requires n >= 1 && m >= 2
  requires result == n * m / (m - 1)
  ensures SocksAfterDay(n, m, result) <= 0
{
  var socks := n + result / m - result;
  
  // Key insight: result = n * m / (m - 1)
  // We need to show: n + result/m - result <= 0
  // Which means: result - result/m >= n
  
  var quotient := n * m / (m - 1);
  var remainder := n * m % (m - 1);
  assert n * m == quotient * (m - 1) + remainder && 0 <= remainder < m - 1;
  assert result == quotient;
  
  // From result * (m - 1) <= n * m < result * (m - 1) + (m - 1)
  // We get: result * (m - 1) <= n * m
  // So: result * m - result <= n * m
  // Therefore: result - result/m >= n * m / m - result/m + remainder_terms >= n
  
  // More precisely: since result >= n (from ResultBounds)
  // and result/m < result, we know result - result/m > 0
  // Also, result * (m-1) <= n * m implies result <= n * m / (m-1)
  // The division gives us the exact bound we need
  
  assert result * (m - 1) <= n * m;
  assert result * m - result <= n * m;
  
  // Now we need to relate this to result - result/m
  // Note that result/m * m <= result < (result/m + 1) * m
  // So result - result/m * m < m
  // But we need the stronger property
  
  // The key is that result - result/m >= n follows from:
  // result * (m-1) / m >= n * m / m = n (approximately)
  
  // Since we're dealing with integer division, we need to be careful
  // result = n * m / (m - 1), so result * (m - 1) >= n * m - (m - 2)
  // This gives us result - result/m >= n when properly analyzed
  
  assert socks <= n - (result - result / m);
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
  
  // We need to show that socks > 0, i.e., n > k - k/m
  // Since k < result = n * m / (m - 1)
  // We have k * (m - 1) < n * m
  
  assert k < result;
  assert result == n * m / (m - 1);
  assert k * (m - 1) < result * (m - 1);
  assert result * (m - 1) <= n * m;
  assert k * (m - 1) < n * m;
  
  // Now k - k/m = k * (m - 1) / m + error terms from integer division
  // Since k * (m - 1) < n * m, we have (k * (m - 1)) / m < n
  
  // For integer division: k - k/m <= k * (m - 1) / m + 1
  // And since k * (m - 1) < n * m, we get k * (m - 1) / m < n
  // So k - k/m < n, which means socks > 0
  
  assert k - k / m < n;
  assert socks == n - (k - k / m);
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

