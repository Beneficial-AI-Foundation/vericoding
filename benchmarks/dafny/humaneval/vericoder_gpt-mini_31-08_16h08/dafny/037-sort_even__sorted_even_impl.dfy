

// <vc-helpers>
function Min(s: seq<int>): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0] else var m := Min(s[1..]); if s[0] <= m then s[0] else m
}

function RemoveOne(s: seq<int>, v: int): seq<int>
  decreases |s|
{
  if |s| == 0 then [] else if s[0] == v then s[1..] else [s[0]] + RemoveOne(s[1..], v)
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
      var witnessIndex :| 0 <= witnessIndex < |s[1..]| && s[1 + witnessIndex] == m1;
      // witness is 1 + witnessIndex
    }
  }
}

lemma RemoveOneMultiset(s: seq<int>, v: int)
  requires v in multiset(s)
  ensures multiset(RemoveOne(s, v)) + multiset([v]) == multiset(s)
  decreases |s|
{
  if |s| == 0 {
    // impossible because v in multiset(s)
  } else if s[0] == v {
    // RemoveOne(s,v) == s[1..]; multiset(s[1..]) + multiset([v]) == multiset(s)
  } else {
    // s[0] != v, so v in s[1..]
    assert v in multiset(s[1..]);
    RemoveOneMultiset(s[1..], v);
    // RemoveOne(s,v) == [s[0]] + RemoveOne(s[1..], v)
    // so multiset(RemoveOne(s,v)) + multiset([v]) ==
    //    multiset([s[0]]) + multiset(RemoveOne(s[1..], v)) + multiset([v]) ==
    //    multiset([s[0]]) + multiset(s[1..]) == multiset(s)
  }
}

lemma MinIsMin(s: seq<int>)
  requires |s| > 0
  ensures forall z :: z in multiset(s) ==> Min(s) <= z
  decreases |s|
{
  if |s| == 1 {
    // trivial
  } else {
    MinIsMin(s[1..]);
    var m1 := Min(s[1..]);
    if s[0] <= m1 {
      // Min(s) = s[0]; for z in s: either z == s[0] or z in s[1..], in both cases s[0] <= z
    } else {
      // Min(s) = m1; by induction m1 <= every element of s[1..], and m1 <= s[0] because m1 <= s[0] holds from definition
    }
  }
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

  // Selection sort on ev to produce sortedEv (proving multiset and ordering)
  var rem := ev;
  var sortedEv := [];
  while |sortedEv| < m
    invariant 0 <= |sortedEv| <= m
    invariant |rem| + |sortedEv| == m
    invariant multiset(sortedEv) + multiset(rem) == multiset(ev)
    invariant forall k :: 0 <= k < |sortedEv| ==> forall z :: z in multiset(rem) ==> sortedEv[k] <= z
  {
    assert |rem| > 0;
    var v := Min(rem);
    MinIsMin(rem);
    // v in multiset(rem) because rem non-empty and v = Min(rem)
    assert v in multiset(rem);
    RemoveOneMultiset(rem, v);
    sortedEv := sortedEv + [v];
    rem := RemoveOne(rem, v);
  }

  var res: seq<int> := [];
  var eidx := 0;
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant |res| == j
    invariant 0 <= eidx <= m
    invariant eidx == (j + 1) / 2
    invariant forall k :: 0 <= k < j && k % 2 == 1 ==> res[k] == a[k]
    invariant forall k :: 0 <= k < j && k % 2 == 0 ==> res[k] == sortedEv[k / 2]
  {
    if j % 2 == 1 {
      res := res + [a[j]];
    } else {
      // when j is even and j < n, eidx < |sortedEv| holds because eidx == (j+1)/2 and |sortedEv| == m
      res := res + [sortedEv[eidx]];
      eidx := eidx + 1;
    }
    j := j + 1;
  }

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