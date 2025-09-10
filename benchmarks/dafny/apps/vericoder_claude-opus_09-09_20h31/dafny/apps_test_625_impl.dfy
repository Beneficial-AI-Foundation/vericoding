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
lemma AlternatingSumEven(n: int)
    requires n > 0 && n % 2 == 0
    ensures AlternatingSum(n) == n / 2
{
    if n == 2 {
        assert AlternatingSum(2) == AlternatingSum(1) + 2 == -1 + 2 == 1;
        assert 2 / 2 == 1;
    } else {
        AlternatingSumEven(n - 2);
        assert AlternatingSum(n - 2) == (n - 2) / 2;
        calc {
            AlternatingSum(n);
        == 
            AlternatingSum(n - 1) + n;
        ==
            AlternatingSum(n - 2) + (-(n - 1)) + n;
        ==
            (n - 2) / 2 + (-(n - 1)) + n;
        ==
            (n - 2) / 2 + 1;
        == { assert (n - 2) / 2 + 1 == n / 2; }
            n / 2;
        }
    }
}

lemma AlternatingSumOdd(n: int)
    requires n > 0 && n % 2 == 1
    ensures AlternatingSum(n) == n / 2 - n
{
    if n == 1 {
        assert AlternatingSum(1) == -1;
        assert 1 / 2 - 1 == 0 - 1 == -1;
    } else {
        AlternatingSumOdd(n - 2);
        assert AlternatingSum(n - 2) == (n - 2) / 2 - (n - 2);
        calc {
            AlternatingSum(n);
        ==
            AlternatingSum(n - 1) + (-n);
        ==
            AlternatingSum(n - 2) + (n - 1) + (-n);
        ==
            (n - 2) / 2 - (n - 2) + (n - 1) + (-n);
        ==
            (n - 2) / 2 - (n - 2) + (n - 1) - n;
        == { assert (n - 2) / 2 - (n - 2) + (n - 1) - n == (n - 2) / 2 - 1; }
            (n - 2) / 2 - 1;
        == { assert n % 2 == 1;
             assert n / 2 == (n - 1) / 2;
             assert (n - 1) / 2 == (n - 2) / 2 + ((n - 1) - (n - 2)) / 2;
             assert (n - 1) / 2 == (n - 2) / 2 + 1 / 2;
             assert (n - 1) / 2 == (n - 2) / 2;
             assert n / 2 == (n - 2) / 2;
             assert (n - 2) / 2 - 1 == n / 2 - 1;
             assert n / 2 - 1 == n / 2 - n + (n - 1);
             assert n - 1 == n - 1;
             assert n / 2 - 1 == n / 2 - n + n - 1;
             assert n / 2 - n == n / 2 - 1 - (n - 1);
             assert n / 2 - n == (n - 2) / 2 - 1; }
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
    var sum := 0;
    var i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant i == 1 ==> sum == 0
        invariant i > 1 ==> sum == AlternatingSum(i - 1)
    {
        if i % 2 == 0 {
            sum := sum + i;
        } else {
            sum := sum - i;
        }
        i := i + 1;
    }
    
    assert i == n + 1;
    assert sum == AlternatingSum(n);
    
    if n % 2 == 0 {
        AlternatingSumEven(n);
    } else {
        AlternatingSumOdd(n);
    }
    
    result := sum;
}
// </vc-code>

