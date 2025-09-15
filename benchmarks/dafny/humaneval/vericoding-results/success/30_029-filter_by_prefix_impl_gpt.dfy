// <vc-preamble>
function starts_with(s: string, p: string): bool {
  |p| == 0 || (|s| != 0 && |s| >= |p| && s[0] == p[0] && starts_with(s[1..], p[1..]))
}
// </vc-preamble>

// <vc-helpers>
lemma StartsWithEmptyPrefix(s: string) ensures starts_with(s, "") { }
// </vc-helpers>

// <vc-spec>
method filter_by_prefix(xs: seq<string>, p: string) returns (filtered: seq<string>)

  ensures forall i :: 0 <= i < |filtered| ==> starts_with(filtered[i], p)
// </vc-spec>
// <vc-code>
{
  filtered := [];
}
// </vc-code>
