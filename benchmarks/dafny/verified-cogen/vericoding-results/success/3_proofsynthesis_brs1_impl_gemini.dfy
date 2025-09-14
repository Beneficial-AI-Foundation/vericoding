// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MyFun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    modifies a, sum
    ensures sum[0] <= N
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Used a local variable for the sum to aid the verifier. */
    var i: int := 0;
    var s: int := 0;
    while i < N
        invariant 0 <= i <= N
        invariant s <= i
        decreases N - i
    {
        if (*)
        {
            a[i] := 1;
        }
        else
        {
            a[i] := 0;
        }
        s := s + a[i];
        i := i + 1;
    }
    sum[0] := s;
}
// </vc-code>
