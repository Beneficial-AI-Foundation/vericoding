// <vc-preamble>
function CountMatches(xs: seq<nat>, x: nat): nat
    decreases |xs|
{
    if |xs| == 0 then
        0
    else
        var firstMatch: nat := if xs[0] == x then 1 else 0;
        firstMatch + CountMatches(xs[1..], x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): obtain an index from a positive CountMatches */
lemma CountMatchesHasIndex(s: seq<nat>, x: nat)
  requires CountMatches(s, x) > 0
  ensures exists i :: 0 <= i < |s| && s[i] == x
  decreases |s|
{
  if |s| == 0 {
    assert false;
  }
  if s[0] == x {
    assert 0 <= 0 < |s|;
    assert s[0] == x;
    return;
  }
  assert CountMatches(s[1..], x) > 0;
  CountMatchesHasIndex(s[1..], x);
  var j :| 0 <= j < |s|-1 && s[1..][j] == x;
  assert 0 <= j+1 < |s|;
  assert s[j+1] == x;
  return;
}

/* helper modified by LLM (iteration 4): from existence of majority value to existence of index holding a majority */
lemma ExistsMajorityIndex(s: seq<nat>)
  requires exists x :: CountMatches(s, x) > |s|/2
  ensures exists k :: 0 <= k < |s| && CountMatches(s, s[k]) > |s|/2
{
  var x :| CountMatches(s, x) > |s|/2;
  CountMatchesHasIndex(s, x);
  var j :| 0 <= j < |s| && s[j] == x;
  assert CountMatches(s, s[j]) == CountMatches(s, x);
  return;
}
// </vc-helpers>

// <vc-spec>
method MajorityElement(xs: array<nat>) returns (result: nat)
    requires 
        xs.Length > 0
    requires
        exists x: nat :: CountMatches(xs[..], x) > xs.Length / 2
    ensures
        CountMatches(xs[..], result) > xs.Length / 2
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): choose a witness index with majority and return its value */
  var n := xs.Length;
  ExistsMajorityIndex(xs[..]);
  var k :| 0 <= k < n && CountMatches(xs[..], xs[k]) > n/2;
  result := xs[k];
}
// </vc-code>
