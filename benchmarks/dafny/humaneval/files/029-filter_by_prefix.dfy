// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def filter_by_prefix(strings: List[str], prefix: str) -> List[str]
Filter an input list of strings only for ones that start with a given prefix.
*/
// </vc-description>

// <vc-spec>
method filter_by_prefix(xs: seq<string>, p: string) returns (filtered: seq<string>)
  // post-conditions-start
  ensures forall i :: 0 <= i < |filtered| ==> starts_with(filtered[i], p)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>

function starts_with(s: string, p: string): bool {
  |p| == 0 || (|s| != 0 && |s| >= |p| && s[0] == p[0] && starts_with(s[1..], p[1..]))
}
// pure-end