// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function OccurrenceCount(s: seq<int>, x: int): nat { |(set i | 0 <= i < |s| && s[i] == x)| }
// </vc-helpers>

// <vc-spec>
method freq(s: seq<int>, x: int) returns (count: int)

    ensures count == |(set i | 0 <= i < |s| && s[i] == x)|
// </vc-spec>
// <vc-code>
{
  count := OccurrenceCount(s, x);
}
// </vc-code>
