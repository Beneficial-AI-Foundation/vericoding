// <vc-helpers>
lemma starts_with_empty_prefix(s: string)
  ensures starts_with(s, "")
{
}

lemma starts_with_properties(s: string, p: string)
  ensures starts_with(s, p) <==> (|p| == 0 || (|s| >= |p| && s[..|p|] == p))
{
  if |p| == 0 {
    starts_with_empty_prefix(s);
  } else if |s| >= |p| {
    starts_with_inductive_helper(s, p);
  }
}

lemma starts_with_inductive_helper(s: string, p: string)
  requires |p| > 0
  requires |s| >= |p|
  ensures starts_with(s, p) <==> s[..|p|] == p
{
  if |p| == 1 {
    assert s[..1] == [s[0]];
    assert p == [p[0]];
  } else {
    starts_with_inductive_helper(s[1..], p[1..]);
    assert s[1..][..|p|-1] == s[1..|p|];
    assert s[..|p|] == [s[0]] + s[1..|p|];
    assert p == [p[0]] + p[1..];
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