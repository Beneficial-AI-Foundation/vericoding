The ensures clause shows: `diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2`

This can be simplified algebraically:
- (n²(n+1)²)/4 - n(n+1)/2
- = n(n+1)/2 * (n(n+1)/2 - 1)
- = n(n+1)/2 * (n(n+1) - 2)/2
- = n(n+1)(n(n+1) - 2)/4

But the most straightforward implementation is to directly compute the formula given in the ensures clause.

//IMPL
method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
  requires n >= 0
  ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
{
  var sumCubes := (n * n * (n + 1) * (n + 1)) / 4;
  var sumNumbers := (n * (n + 1)) / 2;
  diff := sumCubes - sumNumbers;
}