// <vc-helpers>
lemma SumOfFirstNCubes(n: int)
    requires n >= 0
    ensures SumCubes(n) == (n * n * (n + 1) * (n + 1)) / 4

lemma SumOfFirstNNumbers(n: int)
    requires n >= 0
    ensures SumNumbers(n) == (n * (n + 1)) / 2

function SumCubes(n: int): int
    requires n >= 0
{
    if n == 0 then 0 else n * n * n + SumCubes(n - 1)
}

function SumNumbers(n: int): int
    requires n >= 0
{
    if n == 0 then 0 else n + SumNumbers(n - 1)
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    var sumCubes := 0;
    var sumNumbers := 0;
    var i := 1;
    
    while i <= n
        invariant 0 <= i <= n + 1
        invariant sumCubes == SumCubes(i - 1)
        invariant sumNumbers == SumNumbers(i - 1)
    {
        sumCubes := sumCubes + i * i * i;
        sumNumbers := sumNumbers + i;
        i := i + 1;
    }
    
    SumOfFirstNCubes(n);
    SumOfFirstNNumbers(n);
    
    diff := sumCubes - sumNumbers;
}
// </vc-code>
