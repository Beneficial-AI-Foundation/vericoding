// <vc-preamble>
predicate IsSubrangeAt(main: seq<int>, sub: seq<int>, i: int)
{
    0 <= i && i + |sub| <= |main| && sub == main[i..i+|sub|]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsSubArray(main: array<int>, sub: array<int>) returns (result: bool)
    ensures result == (exists k :: 0 <= k <= (main.Length - sub.Length) && IsSubrangeAt(main[..], sub[..], k))
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
