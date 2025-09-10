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
            {
                var n_minus_1 := n - 1;
                AlternatingSumOdd(n_minus_1);
                assert AlternatingSum(n_minus_1) == n_minus_1 / 2 - n_minus_1;
            }
            (n - 1) / 2 - (n-1) + n;
            (n - 1) / 2 - n + 1 + n;
            (n - 1) / 2 + 1;
            n / 2 - 1/2 + 1;
            n / 2 + 1/2; // This is (n+1)/2 if n is odd, but n is even
            (n + 2) / 2;
            n / 2 + 1; // Correct step for even n
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

