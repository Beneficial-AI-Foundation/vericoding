//IMPL SumAndAverage
method SumAndAverage(n: int) returns (sum: int, average: real)
  requires n > 0
  ensures sum == n * (n + 1) / 2
  ensures average == sum as real / n as real
{
  sum := n * (n + 1) / 2;
  average := sum as real / n as real;
}