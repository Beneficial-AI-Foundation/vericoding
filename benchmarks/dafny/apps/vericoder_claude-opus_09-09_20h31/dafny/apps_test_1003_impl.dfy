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
  // We know a >= b * c and c > 0
  // By properties of integer division: (b * c) / c == b
  assert (b * c) / c == b;
  // Since a >= b * c and division is monotonic for positive divisor:
  // a / c >= (b * c) / c == b
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
  
  // We need to show: n + result/m - result <= 0
  // Which is equivalent to: n + result/m <= result
  // Or: n <= result - result/m
  
  // Since result = n * m / (m - 1), we know:
  // result * (m - 1) <= n * m < result * (m - 1) + (m - 1)
  
  // From the definition of integer division:
  assert result * (m - 1) <= n * m;
  assert n * m < (result + 1) * (m - 1);
  
  // Let's work with the inequality directly
  // We need: n <= result - result/m
  
  // result - result/m can be rewritten as:
  // result * (1 - 1/m) = result * (m - 1) / m (approximately)
  
  // Since result * (m - 1) <= n * m:
  // result * (m - 1) / m <= n * m / m = n
  
  // But we need the opposite inequality. Let's reconsider.
  // Actually, we have result = n * m / (m - 1), so:
  // result * (m - 1) = n * m - remainder where 0 <= remainder < m - 1
  
  // More precisely:
  var quotient := n * m / (m - 1);
  assert quotient == result;
  assert result * (m - 1) <= n * m < result * (m - 1) + (m - 1);
  
  // This means: n * m = result * (m - 1) + some_remainder where 0 <= some_remainder < m - 1
  // Therefore: n = (result * (m - 1) + some_remainder) / m
  
  // Since some_remainder < m - 1 < m:
  // n <= (result * (m - 1) + (m - 1)) / m = result * (m - 1) / m + (m - 1) / m
  // n <= result - result/m + (m - 1) / m
  
  // Since (m - 1) / m == 0 for integer division when m >= 2:
  assert (m - 1) / m == 0;
  
  // Therefore: n <= result - result/m
  // Which means: n + result/m <= result
  // So: socks = n + result/m - result <= 0
}

lemma SocksPositiveBefore(n: int, m: int, result: int, k: int)
  requires n >= 1 && m >= 2
  requires result == n * m / (m - 1)
  requires 1 <= k < result
  ensures SocksAfterDay(n, m, k) > 0
{
  var socks := n + k / m - k;
  
  // We need to show that socks > 0, i.e., n + k/m > k
  // Which is equivalent to n > k - k/m
  
  // Since k < result = n * m / (m - 1), we have:
  assert k < n * m / (m - 1);
  
  // This means: k * (m - 1) < n * m
  assert k * (m - 1) < n * m;
  
  // Now k - k/m can be computed as:
  var q := k / m;
  var r := k % m;
  assert k == q * m + r && 0 <= r < m;
  
  // k - k/m = k - q = q * m + r - q = q * (m - 1) + r
  assert k - k / m == q * (m - 1) + r;
  
  // We need to show: q * (m - 1) + r < n
  
  // From k = q * m + r, we get:
  // k * (m - 1) = (q * m + r) * (m - 1) = q * m * (m - 1) + r * (m - 1)
  
  // Since r < m, we have r * (m - 1) < m * (m - 1)
  // And q * (m - 1) + r <= q * m
  
  // From k * (m - 1) < n * m:
  // q * m * (m - 1) + r * (m - 1) < n * m
  // So: q * (m - 1) + r * (m - 1) / m < n
  
  // Since r * (m - 1) / m < m * (m - 1) / m = m - 1 < m:
  // And integer division gives r * (m - 1) / m <= r - 1 < r
  
  // Therefore: q * (m - 1) + r <= q * (m - 1) + r * (m - 1) / m + r/m < n
  
  // More directly: since k < result = n * m / (m - 1)
  // We have k * (m - 1) < n * m
  // And k - k/m = q * (m - 1) + r
  
  // We know (q * (m - 1) + r) * m = q * m * (m - 1) + r * m
  // And q * m + r = k, so:
  // (k - k/m) * m = k * m - q * m = k * m - (k - r) = r * m + k * (m - 1)
  
  // Actually, let's use a simpler approach:
  // k - k/m <= k * (m - 1) / m < n * m / m = n
  
  assert k - k/m < n;
  assert socks == n - (k - k/m);
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

