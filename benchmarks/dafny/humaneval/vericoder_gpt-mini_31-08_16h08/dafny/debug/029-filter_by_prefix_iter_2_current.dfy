

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method filter_by_prefix(xs: seq<string>, p: string) returns (filtered: seq<string>)
  // post-conditions-start
  ensures forall i :: 0 <= i < |filtered| ==> starts_with(filtered[i], p)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var res: seq<string> := [];
  var i := 0;
  while i < |xs|
    invariant 0 <= i <= |xs|
    invariant |res| <= i
    invariant forall j :: 0 <= j < |res| ==> starts_with(res[j], p)
  {
    if starts_with(xs[i], p) {
      res := res + [xs[i]];
    }
    i := i + 1;
  }
  filtered := res;
  return;
}
// </vc-code>

function starts_with(s: string, p: string): bool {
  |p| == 0 || (|s| != 0 && |s| >= |p| && s[0] == p[0] && starts_with(s[1..], p[1..]))
}
// pure-end