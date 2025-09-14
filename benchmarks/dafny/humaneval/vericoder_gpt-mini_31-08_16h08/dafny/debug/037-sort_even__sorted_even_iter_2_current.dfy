

// <vc-helpers>
function Min(s: seq<int>): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0] else var m := Min(s[1..]); if s[0] <= m then s[0] else m
}

function RemoveOne(s: seq<int>, v: int): seq<int>
  requires |s| > 0
  decreases |s|
{
  if s[0] == v then s[1..] else [s[0]] + RemoveOne(s[1..], v)
}

lemma MinIn(s: seq<int>)
  requires |s| > 0
  ensures exists k :: 0 <= k < |s| && s[k] == Min(s)
  decreases |s|
{
  if |s| == 1 {
    // witness 0
  } else {
    MinIn(s[1..]);
    var m1 := Min(s[1..]);
    if s[0] <= m1 {
      // witness 0
    } else {
      // m1 is the minimum, and by induction there is an index in s[1..]
      var witnessIndex :| 0 <= witnessIndex < |s[1..]| && s[1 + witnessIndex] == m1;
      // witness is 1 + witnessIndex
    }
  }
}

function SortSeq(s: seq<int>): seq<int>
  decreases |s|
  ensures |result| == |s|
  ensures multiset(result) == multiset(s)
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
{
  if |s| == 0 then
    []
  else
    [Min(s)] + SortSeq(RemoveOne(s, Min(s)))
}
// </vc-helpers>

// <vc-spec>
method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  var m := (n + 1) / 2;
  var ev: seq<int> := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |ev| == i
    invariant forall k :: 0 <= k < i ==> ev[k] == a[2 * k]
  {
    ev := ev + [a[2 * i]];
    i := i + 1;
  }

  var sortedEv := SortSeq(ev);

  var res: seq<int> := [];
  var eidx := 0;
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant |res| == j
    invariant 0 <= eidx <= m
    invariant forall k :: 0 <= k < j && k % 2 == 1 ==> res[k] == a[k]
    invariant forall k :: 0 <= k < j && k % 2 == 0 ==> res[k] == sortedEv[k / 2]
  {
    if j % 2 == 1 {
      res := res + [a[j]];
    } else {
      res := res + [sortedEv[eidx]];
      eidx := eidx + 1;
    }
    j := j + 1;
  }

  // final checks to help verifier
  // multiset(res) == multiset(sortedEv) + multiset(odds) == multiset(ev) + multiset(odds) == multiset(a)
  // odd positions preserved by invariants above
  return res;
}
// </vc-code>

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
{
  assume{:axiom} false;
}