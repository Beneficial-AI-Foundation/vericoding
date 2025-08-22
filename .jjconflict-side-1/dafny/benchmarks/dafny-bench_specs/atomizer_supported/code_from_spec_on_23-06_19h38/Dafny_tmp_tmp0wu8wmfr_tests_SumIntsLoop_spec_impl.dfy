// ATOM 
function sumInts( n: int ): int
    requires n >= 0;
{
    if n == 0 then
        0
    else
        sumInts(n-1)+n
}

/* code modified by LLM (iteration 2): Added helper lemma to prove the recursive relationship of sumInts */
lemma SumIntsRecursive(n: int)
    requires n > 0
    ensures sumInts(n) == sumInts(n-1) + n
{
    // This follows directly from the definition of sumInts
}

/* code modified by LLM (iteration 2): Added helper lemma to prove the closed form formula */
lemma SumIntsFormula(n: int)
    requires n >= 0
    ensures sumInts(n) == n * (n + 1) / 2
{
    if n == 0 {
        // Base case: sumInts(0) == 0 == 0 * 1 / 2
    } else {
        // Inductive step
        SumIntsFormula(n - 1);
        assert sumInts(n - 1) == (n - 1) * n / 2;
        assert sumInts(n) == sumInts(n - 1) + n;
        assert sumInts(n) == (n - 1) * n / 2 + n;
        assert sumInts(n) == (n - 1) * n / 2 + 2 * n / 2;
        assert sumInts(n) == ((n - 1) * n + 2 * n) / 2;
        assert sumInts(n) == (n * n - n + 2 * n) / 2;
        assert sumInts(n) == (n * n + n) / 2;
        assert sumInts(n) == n * (n + 1) / 2;
    }
}

//IMPL SumIntsLoop
method SumIntsLoop( n: int ) returns ( s: int )
    requires n >= 0;
    ensures s == sumInts(n)
    ensures s == n*(n+1)/2;
{
    /* code modified by LLM (iteration 2): Fixed loop logic - increment i after updating s, and fixed invariant maintenance */
    s := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant s == sumInts(i)
    {
        i := i + 1;
        s := s + i;
        SumIntsRecursive(i);
    }
    /* code modified by LLM (iteration 2): Added lemma call to establish the closed form */
    SumIntsFormula(n);
}

//IMPL Main
method Main()
{
}