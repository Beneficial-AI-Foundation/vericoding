// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ExistsSubSlice(main: array<int>, sub: array<int>): bool
  reads main, sub
{
  exists k: int, l: int ::
    0 <= k <= main.Length - sub.Length &&
    l == k + sub.Length &&
    main[k..l] == sub[..]
}
// </vc-helpers>

// <vc-spec>
method IsSubArray(main: array<int>, sub: array<int>) returns (result: bool)
    requires sub.Length <= main.Length
    ensures result == (exists k: int, l: int ::
        0 <= k <= (main.Length - sub.Length) && l == k + sub.Length && 
        main[k..l] == sub[..])
// </vc-spec>
// <vc-code>
{
  result := ExistsSubSlice(main, sub);
}
// </vc-code>
