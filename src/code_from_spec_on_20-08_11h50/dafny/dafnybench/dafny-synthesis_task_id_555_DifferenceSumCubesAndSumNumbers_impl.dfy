function SumNumbers(n: int): int
    requires n >= 0
{
    if n == 0 then 0 else n + SumNumbers(n - 1)
}

function SumCubes(n: int): int
    requires n >= 0
{
    if n == 0 then 0 else n * n * n + SumCubes(n - 1)
}

lemma SumNumbersFormula(n: int)
    requires n >= 0
    ensures SumNumbers(n) == (n * (n + 1)) / 2
{
    if n == 0 {
        // Base case
    } else {
        SumNumbersFormula(n - 1);
        // Inductive step
        calc {
            SumNumbers(n);
            n + SumNumbers(n - 1);
            n + ((n - 1) * n) / 2;
            (2 * n + (n - 1) * n) / 2;
            (2 * n + n * n - n) / 2;
            (n + n * n) / 2;
            (n * (1 + n)) / 2;
            (n * (n + 1)) / 2;
        }
    }
}

lemma SumCubesFormula(n: int)
    requires n >= 0
    ensures SumCubes(n) == (n * n * (n + 1) * (n + 1)) / 4
{
    if n == 0 {
        // Base case
    } else {
        SumCubesFormula(n - 1);
        // Inductive step
        calc {
            SumCubes(n);
            n * n * n + SumCubes(n - 1);
            n * n * n + ((n - 1) * (n - 1) * n * n) / 4;
            (4 * n * n * n + (n - 1) * (n - 1) * n * n) / 4;
            (n * n * (4 * n + (n - 1) * (n - 1))) / 4;
            (n * n * (4 * n + n * n - 2 * n + 1)) / 4;
            (n * n * (n * n + 2 * n + 1)) / 4;
            (n * n * (n + 1) * (n + 1)) / 4;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
    SumCubesFormula(n);
    SumNumbersFormula(n);
    
    var sumCubes := (n * n * (n + 1) * (n + 1)) / 4;
    var sumNumbers := (n * (n + 1)) / 2;
    diff := sumCubes - sumNumbers;
}
// </vc-code>