

// <vc-helpers>
lemma starts_with_empty_prefix(s: string)
  ensures starts_with(s, "")
{
}

lemma starts_with_properties(s: string, p: string)
  requires starts_with(s, p)
  ensures |s| >= |p|
{
  if |p| == 0 {
  } else {
    starts_with_properties(s[1..], p[1..]);
  }
}
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
  filtered := [];
  var i := 0;
  while i < |xs|
    invariant 0 <= i <= |xs|
    invariant forall j :: 0 <= j < |filtered| ==> starts_with(filtered[j], p)
  {
    if starts_with(xs[i], p) {
      filtered := filtered + [xs[i]];
    }
    i := i + 1;
  }
}
// </vc-code>

function starts_with(s: string, p: string): bool {
  |p| == 0 || (|s| != 0 && |s| >= |p| && s[0] == p[0] && starts_with(s[1..], p[1..]))
}
// pure-end