

// <vc-helpers>
function starts_with_by_prefix_helper(s: string, p: string): bool
{
    if |p| == 0 then
        true
    else if |s| < |p| then
        false
    else
        s[0] == p[0] && starts_with_by_prefix_helper(s[1..], p[1..])
}

// Proof that the provided `starts_with` function is equivalent to `starts_with_by_prefix_helper`.
// This is needed because the provided `starts_with` function is not directly suitable for
// reasoning about recursion with `filter_by_prefix`, due to its slightly different
// structure for base cases and recursive calls which can lead to verification issues.
lemma lemma_starts_with_equivalence(s: string, p: string)
  ensures starts_with(s, p) <==> starts_with_by_prefix_helper(s, p)
{
  if |p| == 0 {
    // Both are true
  } else if |s| == 0 {
    // starts_with is false, starts_with_by_prefix_helper is false
  } else {
    calc {
      starts_with(s,p);
      (|p| == 0 || (|s| != 0 && |s| >= |p| && s[0] == p[0] && starts_with(s[1..], p[1..])));
      {
        if |s| < |p| {
          // This case implies that starts_with(s,p) is false
          // and starts_with_by_prefix_helper(s,p) is false
        } else {
          assert |s| >= |p|;
          assert s[0] == p[0];
          assert starts_with(s[1..], p[1..]);
          lemma_starts_with_equivalence(s[1..], p[1..]);
          assert starts_with(s[1..], p[1..]) <==2> starts_with_by_prefix_helper(s[1..], p[1..]);
        }
      }
      starts_with_by_prefix_helper(s, p);
    }
  }
}

lemma lemma_starts_with_equivalence_for_all(coll: seq<string>, p: string)
  requires forall k :: 0 <= k < |coll| ==> starts_with_by_prefix_helper(coll[k], p)
  ensures forall k :: 0 <= k < |coll| ==> starts_with(coll[k], p)
{
  forall k | 0 <= k < |coll|
    ensures starts_with(coll[k], p)
  {
    lemma_starts_with_equivalence(coll[k], p);
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
  var filtered_list: seq<string> := [];
  var i := 0;
  while i < |xs|
    invariant 0 <= i <= |xs|
    invariant forall k :: 0 <= k < |filtered_list| ==> starts_with_by_prefix_helper(filtered_list[k], p)
    invariant forall k :: 0 <= k < |filtered_list| ==> exists j :: 0 <= j < i && filtered_list[k] == xs[j]
  {
    if starts_with_by_prefix_helper(xs[i], p) {
      filtered_list := filtered_list + [xs[i]];
    }
    i := i + 1;
  }
  lemma_starts_with_equivalence_for_all(filtered_list, p); // Add a post-loop assertion
  return filtered_list;
}
// </vc-code>

function starts_with(s: string, p: string): bool {
  |p| == 0 || (|s| != 0 && |s| >= |p| && s[0] == p[0] && starts_with(s[1..], p[1..]))
}
// pure-end