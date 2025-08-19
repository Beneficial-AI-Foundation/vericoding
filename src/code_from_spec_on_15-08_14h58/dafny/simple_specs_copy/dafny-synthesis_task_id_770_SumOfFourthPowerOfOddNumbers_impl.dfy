//IMPL 
method SumOfFourthPowerOfOddNumbers(n: int) returns (sum: int)
  requires n > 0
  ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15
{
  sum := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sum == i * (2 * i + 1) * (24 * i * i * i - 12 * i * i - 14 * i + 7) / 15
  {
    var odd := 2 * i + 1;
    sum := sum + odd * odd * odd * odd;
    i := i + 1;
  }
}