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
function AlternatingSum(n: int): int
    requires n > 0
{
    if n == 1 then -1
    else AlternatingSum(n-1) + (if n % 2 == 0 then n else -n)
}

function Summation(n: int): int
    requires n >= 0
    ensures Summation(n) == (n * (n + 1)) / 2
{
    if n == 0 then 0
    else n + Summation(n - 1)
}

lemma AlternatingSumEven(n: int)
    requires n > 0 && n % 2 == 0
    ensures AlternatingSum(n) == n / 2
{
    if n == 2 {
        calc {
            AlternatingSum(2);
            AlternatingSum(1) + (if 2 % 2 == 0 then 2 else -2);
            -1 + 2;
            1;
            2 / 2;
        }
    } else {
        AlternatingSumEven(n - 2);
        calc {
            AlternatingSum(n);
            AlternatingSum(n-1) + n;
            (AlternatingSum(n-2) + -(n-1)) + n; // AlternatingSum(n-1) = AlternatingSum(n-2) + (if (n-1)%2 == 0 then (n-1) else -(n-1))
                                            // Since n is even, n-1 is odd, so we use -(n-1)
            AlternatingSum(n-2) - n + 1 + n;
            AlternatingSum(n-2) + 1;
            (n - 2) / 2 + 1;
            n / 2 - 1 + 1;
            n / 2;
        }
    }
}

lemma AlternatingSumOdd(n: int)
    requires n > 0 && n % 2 != 0
    ensures AlternatingSum(n) == n / 2 - n
{
    if n == 1 {
        assert AlternatingSum(1) == -1;
        assert 1 / 2 - 1 == 0 - 1 == -1;
    } else {
        AlternatingSumEven(n - 1);
        calc {
            AlternatingSum(n);
            AlternatingSum(n-1) + (-n);
            (n - 1) / 2 + (-n);
            n / 2 - 1/2 - n;
            n / 2 - n;
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
    if n % 2 == 0 {
        AlternatingSumEven(n);
        return n / 2;
    } else {
        AlternatingSumOdd(n);
        return n / 2 - n;
    }
}
// </vc-code>

