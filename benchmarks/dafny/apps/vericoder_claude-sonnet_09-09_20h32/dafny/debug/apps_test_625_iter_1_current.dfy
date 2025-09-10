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
lemma AlternatingSumEvenProperty(n: int)
    requires n > 0 && n % 2 == 0
    ensures AlternatingSum(n) == n / 2
{
    if n == 2 {
        // Base case
    } else {
        AlternatingSumOddProperty(n-1);
        assert AlternatingSum(n-1) == (n-1) / 2 - (n-1);
        assert AlternatingSum(n) == AlternatingSum(n-1) + n;
        assert (n-1) / 2 - (n-1) + n == (n-1) / 2 + 1;
        assert (n-1) / 2 + 1 == n / 2;
    }
}

lemma AlternatingSumOddProperty(n: int)
    requires n > 0 && n % 2 != 0
    ensures AlternatingSum(n) == n / 2 - n
{
    if n == 1 {
        // Base case
    } else {
        AlternatingSumEvenProperty(n-1);
        assert AlternatingSum(n-1) == (n-1) / 2;
        assert AlternatingSum(n) == AlternatingSum(n-1) - n;
        assert (n-1) / 2 - n == n / 2 - n;
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
    result := 0;
    var i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant result == AlternatingSum(i - 1)
        decreases n - i
    {
        if i % 2 == 0 {
            result := result + i;
        } else {
            result := result - i;
        }
        i := i + 1;
    }
    
    if n % 2 == 0 {
        AlternatingSumEvenProperty(n);
    } else {
        AlternatingSumOddProperty(n);
    }
}
// </vc-code>

