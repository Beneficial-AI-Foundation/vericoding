//IMPL SumOfFourthPowerOfOddNumbers
method SumOfFourthPowerOfOddNumbers(n: int) returns (sum: int)
    requires n > 0
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n  - 14 * n + 7) / 15
{
    sum := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant sum == SumOfFourthPowerOfOddNumbersUpTo(i)
    {
        var oddNumber := 2 * i + 1;
        var fourthPower := oddNumber * oddNumber * oddNumber * oddNumber;
        sum := sum + fourthPower;
        i := i + 1;
    }
}

function SumOfFourthPowerOfOddNumbersUpTo(k: int): int
    requires k >= 0
{
    if k == 0 then 0
    else 
        var oddNumber := 2 * k - 1;
        SumOfFourthPowerOfOddNumbersUpTo(k - 1) + oddNumber * oddNumber * oddNumber * oddNumber
}