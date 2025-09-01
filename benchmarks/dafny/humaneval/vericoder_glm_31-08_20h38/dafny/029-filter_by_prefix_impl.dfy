

// <vc-helpers>
ghost method filter_by_prefix_helper(xs: seq<string>, p: string) returns (filtered: seq<string>)
  ensures forall i :: 0 <= i < |filtered| ==> starts_with(filtered[i], p)
  ensures forall i :: 0 <= i < |xs| ==> starts_with(xs[i], p) ==> exists j :: 0 <= j < |filtered| && filtered[j] == xs[i]
{
  filtered := [];
  var idx := 0;
  while idx < |xs|
    invariant 0 <= idx <= |xs|
    invariant filtered == [xs[j] | j in 0..idx :: starts_with(xs[j], p)]
  {
    if starts_with(xs[idx], p) {
      filtered := filtered + [xs[idx]];
    }
    idx := idx + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method filter_by_prefix(xs: seq<string>, p: string) returns (filtered: seq<string>)
  // post-conditions-start
  ensures forall i :: 0 <= i < |filtered| ==> starts_with(filtered[i], p)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var result: seq<string> := [];
  var i := 0;
  while i < |xs|
    invariant 0 <= i <= |xs|
    invariant result == [xs[j] | j in 0..i :: starts_with(xs[j], p)]
  {
    if starts_with(xs[i], p) {
      result := result + [xs[i]];
    }
    i := i + 1;
  }
  filtered := result;
}
// </vc-code>

function starts_with(s: string, p: string): bool {
  |p| == 0 || (|s| != 0 && |s| >= |p| && s[0] == p[0] && starts_with(s[1..], p[1..]))
}
// pure-end