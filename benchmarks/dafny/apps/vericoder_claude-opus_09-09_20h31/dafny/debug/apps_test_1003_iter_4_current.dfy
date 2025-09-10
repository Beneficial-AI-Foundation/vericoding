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
  // The key insight: if a >= b * c, then a/c >= b
  // This follows from the fact that integer division of b*c by c gives exactly b
  // and a >= b*c means a/c >= (b*c)/c = b
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
  
  // Since result = n * m / (m - 1), we have:
  // result * (m - 1) <= n * m < result * (m - 1) + (m - 1)
  
  // From result * (m - 1) <= n * m:
  // result - result/m = result * (m - 1) / m + (potential rounding)
  // And result * (m - 1) / m >= n * m / m = n
  
  // The key observation is:
  // result - result/m = result * (1 - 1/m) >= result * (m-1)/m >= n
  
  // Let's compute more directly:
  var q := result / m;
  var r := result % m;
  assert result == q * m + r && 0 <= r < m;
  
  // result - result/m = result - q = q * m + r - q = q * (m - 1) + r
  // We need to show this is >= n
  
  // Since result = n * m / (m - 1), we have:
  assert result * (m - 1) <= n * m;
  assert result * (m - 1) + (m - 1) > n * m;
  
  // This gives us: result - result/m >= n
  assert socks <= 0;
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
  // k < n * m / (m - 1)
  // So k * (m - 1) < n * m
  
  // Now k - k/m = k * (1 - 1/m) = k * (m-1)/m (with potential rounding)
  // More precisely, for integer division:
  var q := k / m;
  var r := k % m;
  assert k == q * m + r && 0 <= r < m;
  
  // k - k/m = k - q = q * m + r - q = q * (m - 1) + r
  
  // We need to show: k - k/m < n
  // Since k * (m - 1) < n * m (from k < result), we have:
  // (k - k/m) * m <= k * (m - 1) < n * m
  // Therefore k - k/m < n
  
  assert k * (m - 1) < n * m;
  
  // The bound k - k/m < n follows because:
  // k - k/m <= k * (m - 1) / m < n * m / m = n
  assert (q * (m - 1) + r) * m == q * m * (m - 1) + r * m;
  assert q * m * (m - 1) + r * m <= k * (m - 1);
  assert k * (m - 1) < n * m;
  
  assert k - k / m == q * (m - 1) + r;
  assert (q * (m - 1) + r) < n;
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

