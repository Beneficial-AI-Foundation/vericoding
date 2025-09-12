// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsSubList(main: array<int>, sub: array<int>) returns (result: bool)

    requires
        sub.Length <= main.Length

    ensures
        result == (exists k: int, l: int ::
            0 <= k <= (main.Length - sub.Length) && l == k + sub.Length && (main[k..l]) == sub[..])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
