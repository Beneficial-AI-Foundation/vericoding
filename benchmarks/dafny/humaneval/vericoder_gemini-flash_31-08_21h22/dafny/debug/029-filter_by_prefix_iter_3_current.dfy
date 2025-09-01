

// <vc-helpers>
function {:pure} starts_with_helper(s: string, p: string): bool
{
  if |p| == 0 then
    true
  else if |s| == 0 then
    false
  else if |s| < |p| then
    false
  else
    s[0] == p[0] && starts_with_helper(s[1..], p[1..])
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
  var filtered_list: seq<string> := [];
  for i := 0 to |xs| - 1
    invariant forall j :: 0 <= j < |filtered_list| ==> starts_with_helper(filtered_list[j], p)
    invariant forall j :: 0 <= j < |filtered_list| ==> (exists k :: 0 <= k < i && xs[k] == filtered_list[j] && starts_with_helper(xs[k], p))
    invariant forall k :: 0 <= k < i && starts_with_helper(xs[k], p) ==> (exists j :: 0 <= j < |filtered_list| && filtered_list[j] == xs[k])
    invariant forall k :: 0 <= k < i && !starts_with_helper(xs[k], p) ==> (forall j :: 0 <= j < |filtered_list| && filtered_list[j] != xs[k])
  {
    if starts_with_helper(xs[i], p) {
      filtered_list := filtered_list + [xs[i]];
    }
  }
  return filtered_list;
}
// </vc-code>

function starts_with(s: string, p: string): bool {
  |p| == 0 || (|s| != 0 && |s| >= |p| && s[0] == p[0] && starts_with(s[1..], p[1..]))
}
// pure-end