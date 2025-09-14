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
lemma EvenSum(n: int)
    requires n % 2 == 0 && n > 0
    ensures AlternatingSum(n) == n / 2
{
    if n == 2 {
        // AlternatingSum(2) = AlternatingSum(1) + 2 = -1 + 2 = 1
        assert AlternatingSum(1) == -1;
        assert AlternatingSum(2) == AlternatingSum(1) + 2;
        assert AlternatingSum(2) == 1;
        assert 2 / 2 == 1;
    } else {
        EvenSum(n-2);
        assert AlternatingSum(n-1) == AlternatingSum(n-2) - (n-1);
        assert AlternatingSum(n-2) == (n-2) / 2;
        assert AlternatingSum(n) == AlternatingSum(n-1) + n;
        assert AlternatingSum(n) == ((n-2)/2 - (n-1)) + n;
        assert AlternatingSum(n) == (n-2)/2 + n - n + 1;
        assert AlternatingSum(n) == (n-2)/2 + 1;
        assert AlternatingSum(n) == n/2;
    }
}

lemma OddSum(n: int)
    requires n % 2 == 1 && n > 0
    ensures AlternatingSum(n) == n / 2 - n
{
    if n == 1 {
        assert AlternatingSum(1) == -1;
        assert 0 - 1 == -1;
    } else {
        assert AlternatingSum(n) == AlternatingSum(n-1) - n;
        EvenSum(n-1);
        assert AlternatingSum(n-1) == (n-1) / 2;
        assert AlternatingSum(n) == (n-1)/2 - n;
        assert (n-1)/2 == n/2;
        assert AlternatingSum(n) == n/2 - n;
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
    if n == 1 {
        result := -1;
    } else {
        var prev := solve(n-1);
        if n % 2 == 0 {
            result := prev + n;
        } else {
            result := prev - n;
        }
    }
    if n % 2 == 0 {
        EvenSum(n);
        assert result == n / 2;
    } else {
        OddSum(n);
        assert result == n / 2 - n;
    }
}
// </vc-code>

