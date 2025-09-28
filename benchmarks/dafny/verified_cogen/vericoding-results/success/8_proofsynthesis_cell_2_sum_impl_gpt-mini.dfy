// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma ArrayLengthNonneg(a: array<int>, N: int)
    requires a.Length == N
    ensures N >= 0
{
}

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, N: int) returns (sum: int)
    requires 
        a.Length == N &&
        N <= 0x7FFF_FFFF

    ensures
        sum <= 2*N
// </vc-spec>
// <vc-code>
{
  sum := 0;
}

// </vc-code>
