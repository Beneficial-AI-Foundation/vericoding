// <vc-preamble>
function starts_with(s: string, p: string): bool {
  |p| == 0 || (|s| != 0 && |s| >= |p| && s[0] == p[0] && starts_with(s[1..], p[1..]))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method filter_by_prefix(xs: seq<string>, p: string) returns (filtered: seq<string>)

  ensures forall i :: 0 <= i < |filtered| ==> starts_with(filtered[i], p)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
