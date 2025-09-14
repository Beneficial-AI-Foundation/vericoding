function AlternatingSum(n: int): int
    requires n > 0
{
    if n == 1 then -1
    else AlternatingSum(n-1) + (if n % 2 == 0 then n else -n)
}

predicate ValidInput(n: int) {
    n > 0
}

// <vc-helpers>
lemma AlternatingSumFormula(n: int)
    requires ValidInput(n)
    ensures AlternatingSum(n) == if n % 2 == 0 then n / 2 else n / 2 - n
{
    if n == 1 {
    } else {
        AlternatingSumFormula(n - 1);
        if n % 2 == 0 {
            calc {
                AlternatingSum(n);
                AlternatingSum(n - 1) + n;
                { AlternatingSumFormula(n - 1); }
                (n - 1) / 2 - (n - 1) + n;
                (n / 2 - 1) - (n - 1) + n;
                n / 2 - 1 - n + 1 + n;
                n / 2;
            }
        } else {
            calc {
                AlternatingSum(n);
                AlternatingSum(n - 1) - n;
                { AlternatingSumFormula(n - 1); }
                (n - 1) / 2 - n;
                (n / 2) - n;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == AlternatingSum(n)
    ensures n % 2 == 0 ==> result == n / 2
    ensures n % 2 != 0 ==> result == n / 2 - n
// </vc-spec>
// <vc-code>
{
    AlternatingSumFormula(n);
    result := AlternatingSum(n);
}
// </vc-code>

