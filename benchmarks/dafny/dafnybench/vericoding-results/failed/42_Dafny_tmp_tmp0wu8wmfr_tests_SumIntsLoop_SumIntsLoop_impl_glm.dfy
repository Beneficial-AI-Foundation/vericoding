function sumInts( n: int ): int
    requires n >= 0;
{
    if n == 0 then
        0
    else
        sumInts(n-1)+n
}

// <vc-helpers>
lemma SumIsClosedForm(i: int)
    requires i >= 0
    ensures sumInts(i) == i*(i+1)/2
    decreases i
{
    if i == 0 {
        calc {
            sumInts(0);
            0
        };
    } else {
        SumIsClosedForm(i-1);
        calc {
            sumInts(i);
            sumInts(i-1) + i;
            (i-1)*i/2 + i;
            (i-1)*i/2 + 2*i/2;
            ((i-1)*i + 2*i) / 2;
            (i*i - i + 2*i) / 2;
            (i*i + i) / 2;
            i*(i+1)/2;
        };
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
    var i := 0;
    s := 0;
    while i < n
        invariant 0 <= i <= n
        invariant s == sumInts(i)
        invariant s == i*(i+1)/2
    {
        i := i + 1;
        s := s + i;
    }
}
// </vc-code>

