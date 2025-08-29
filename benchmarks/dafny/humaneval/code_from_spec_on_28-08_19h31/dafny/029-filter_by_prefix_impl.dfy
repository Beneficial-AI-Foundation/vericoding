// <vc-helpers>
function startsWith(s: string, p: string): bool {
  |p| == 0 || (|s| != 0 && |s| >= |p| && s[0] == p[0] && startsWith(s[1..], p[1..]))
}
// </vc-helpers>

// <vc-spec>
method filter_by_prefix(xs: seq<string>, p: string) returns (filtered: seq<string>)
  // post-conditions-start
  ensures forall i :: 0 <= i < |filtered| ==> starts_with(filtered[i], p)
  // post-conditions-end
// </vc-spec>
// <vc-code>
method FilterByPrefix(xs: seq<string>, p: string) returns (filtered: seq<string>)
  ensures forall i :: 0 <= i < |filtered| ==> startsWith(filtered[i], p)
{
  var result: seq<string> := [];
  var i: int := 0;
  while i < |xs|
    invariant 0 <= i <= |xs|
    invariant forall k :: 0 <= k < |result| ==> startsWith(result[k], p)
  {
    if startsWith(xs[i], p) {
      result := result + [xs[i]];
    }
    i := i + 1;
  }
  return result;
}
// </vc-code>

function starts_with(s: string, p: string): bool {
  |p| == 0 || (|s| != 0 && |s| >= |p| && s[0] == p[0] && starts_with(s[1..], p[1..]))
}
// pure-end