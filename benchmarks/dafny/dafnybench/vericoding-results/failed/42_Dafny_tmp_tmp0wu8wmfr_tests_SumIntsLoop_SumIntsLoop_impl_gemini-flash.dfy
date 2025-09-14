function sumInts( n: int ): int
    requires n >= 0;
{
    if n == 0 then
        0
    else
        sumInts(n-1)+n
}

// <vc-helpers>
function sumIntsAcc( n: int ): int
    requires n >= 0
{
    if n == 0 then
        0
    else
        sumIntsAcc(n-1)+n
}

lemma SumIntsFormula(n: int)
    requires n >= 0
    ensures sumIntsAcc(n) == n*(n+1)/2
{
    if n == 0 {
    } else {
        SumIntsFormula(n-1);
        calc {
            sumIntsAcc(n);
            sumIntsAcc(n-1) + n;
            (n-1)*n/2 + n;
            (n*n - n + 2*n)/2;
            (n*n + n)/2;
            n*(n+1)/2;
        }
    }
}

lemma SumIntsAccIsSumInts(n: int)
    requires n >= 0
    ensures sumIntsAcc(n) == sumInts(n)
{
    if n == 0 {
    } else {
        SumIntsAccIsSumInts(n-1);
    }
}
// </vc-helpers>

// <vc-spec>
method SumIntsLoop( n: int ) returns ( s: int )
    requires n >= 0;
    ensures s == sumInts(n)
    ensures s == n*(n+1)/2;
// </vc-spec>
// <vc-code>
{
    var sum := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant sum == i*(i+1)/2
        invariant sum == sumIntsAcc(i)
    {
        sum := sum + (i + 1);
        i := i + 1;
    }
    s := sum;
    SumIntsFormula(n);
    SumIntsAccIsSumInts(n);
}
// </vc-code>

