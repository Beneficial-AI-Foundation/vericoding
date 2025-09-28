// <vc-preamble>
function starts_with(s: string, p: string): bool {
  |p| == 0 || (|s| != 0 && |s| >= |p| && s[0] == p[0] && starts_with(s[1..], p[1..]))
}
// </vc-preamble>

// <vc-helpers>
function filter_helper(xs: seq<string>, p: string, idx: int): seq<string>
  requires 0 <= idx <= |xs|
  ensures forall i :: 0 <= i < |filter_helper(xs, p, idx)| ==> starts_with(filter_helper(xs, p, idx)[i], p)
  decreases |xs| - idx
{
  if idx == |xs| then
    []
  else if starts_with(xs[idx], p) then
    [xs[idx]] + filter_helper(xs, p, idx+1)
  else
    filter_helper(xs, p, idx+1)
}
// </vc-helpers>

// <vc-spec>
method filter_by_prefix(xs: seq<string>, p: string) returns (filtered: seq<string>)

  ensures forall i :: 0 <= i < |filtered| ==> starts_with(filtered[i], p)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed helper with termination */
  filtered := filter_helper(xs, p, 0);
}
// </vc-code>
