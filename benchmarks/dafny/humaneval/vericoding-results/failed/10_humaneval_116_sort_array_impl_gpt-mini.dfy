// <vc-preamble>
function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove element at index */
function removeAt(s: seq<nat>, i: int): seq<nat>
  requires 0 <= i < |s|
{
  s[..i] + s[i+1..]
}

/* helper modified by LLM (iteration 5): find index of minimal popcount element */
function minIndex(s: seq<nat>): int
  requires |s| > 0
  decreases |s|
  ensures 0 <= result < |s|
  ensures forall j :: 0 <= j < |s| ==> popcount(s[result]) <= popcount(s[j])
{
  if |s| == 1 then 0
  else
    var t := minIndex(s[1..]);
    var idx := t + 1;
    if popcount(s[0]) <= popcount(s[idx]) then 0 else idx
}

/* helper modified by LLM (iteration 5): lemma about removal preserving multiset */
lemma RemoveAtMultiset(s: seq<nat>, i: int)
  requires 0 <= i < |s|
  ensures multiset(s) == multiset([s[i]] + removeAt(s,i))
{
  assert s == s[..i] + [s[i]] + s[i+1..];
  assert removeAt(s,i) == s[..i] + s[i+1..];
  assert [s[i]] + removeAt(s,i) == s[..i] + [s[i]] + s[i+1..];
  assert multiset(s) == multiset([s[i]] + removeAt(s,i));
}

// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<nat>) returns (sorted: seq<nat>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): selection sort using helpers */
{
  var remaining := s;
  var acc: seq<nat> := [];
  while |remaining| > 0
    invariant |acc| + |remaining| == |s|
    invariant multiset(acc + remaining) == multiset(s)
    invariant forall i, j :: 0 <= i < j < |acc| ==> popcount(acc[i]) <= popcount(acc[j])
    invariant |acc| == 0 || (forall k :: 0 <= k < |remaining| ==> popcount(acc[|acc|-1]) <= popcount(remaining[k]))
    decreases |remaining|
  {
    var idx := minIndex(remaining);
    var x := remaining[idx];
    RemoveAtMultiset(remaining, idx);
    if |acc| > 0 {
      assert popcount(acc[|acc|-1]) <= popcount(x);
    }
    acc := acc + [x];
    remaining := removeAt(remaining, idx);
  }
  sorted := acc;
}

// </vc-code>
