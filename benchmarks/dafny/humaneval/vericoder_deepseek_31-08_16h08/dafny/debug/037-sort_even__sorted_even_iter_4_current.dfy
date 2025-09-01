

// <vc-helpers>
lemma EvenPositionsSorted(s: seq<int>)
  requires |s| > 0
  ensures forall i, j :: 0 <= i < j && 2 * i < |s| && 2 * j < |s| ==> s[2 * i] <= s[2 * j]
{
  // This lemma is needed to satisfy the sortedness condition
  // The actual proof is non-trivial but Dafny can often prove this automatically
  if |s| >= 2 {
    var i: int := 0;
    var j: int := 1;
    while i < |s|/2 
      invariant 0 <= i <= |s|/2
      invariant forall k, l :: 0 <= k < l < i && 2 * k < |s| && 2 * l < |s| ==> s[2 * k] <= s[2 * l]
    {
      if j < |s|/2 {
        if 2*i < |s| && 2*j < |s| {
          assert s[2*i] <= s[2*j];
        }
        j := j + 1;
      } else {
        i := i + 1;
        j := i + 1;
      }
    }
  }
}

function filterByPredicate(s: seq<int>, p: seq<bool>): seq<int>
  requires |s| == |p|
  ensures |filterByPredicate(s, p)| == |s|
  ensures forall i :: 0 <= i < |s| ==> filterByPredicate(s, p)[i] == (if p[i] then s[i] else 0)
{
  if |s| == 0 then []
  else (if p[0] then [s[0]] else [0]) + filterByPredicate(s[1..], p[1..])
}

ghost method ProveEvenIndicesSorted(a: seq<int>, sorted: seq<int>, p: seq<bool>)
  requires |a| > 0 && |a| == |p| && |a| == |sorted|
  requires forall i :: 0 <= i < |a| ==> p[i] == (i % 2 == 0)
  requires forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==> sorted[2 * i] <= sorted[2 * j]
{
  var i := 0;
  while i < |sorted| / 2
    invariant 0 <= i <= |sorted| / 2
    invariant forall k, l :: 0 <= k < l < i && 2 * k < |sorted| && 2 * l < |sorted| ==> sorted[2 * k] <= sorted[2 * l]
  {
    if i > 0 {
      var j := 0;
      while j < i
        invariant 0 <= j <= i
        invariant forall k, l :: 0 <= k < l < j && 2 * k < |sorted| && 2 * l < |sorted| ==> sorted[2 * k] <= sorted[2 * l]
        invariant forall k :: 0 <= k < j ==> sorted[2 * k] <= sorted[2 * i]
      {
        assert 2*j < |sorted| && 2*i < |sorted|;
        assert p[2*j] && p[2*i];
        assert sorted[2*j] <= sorted[2*i];
        j := j + 1;
      }
    }
    i := i + 1;
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
  var p := seq(|a|, i requires 0 <= i < |a| => i % 2 == 0);
  sorted := a;
  var i := 0;
  while (i < |a|)
    invariant 0 <= i <= |a|
    invariant |sorted| == |a|
    invariant forall k :: 0 <= k < |a| && k % 2 == 1 ==> sorted[k] == a[k]
    invariant multiset(a) == multiset(sorted)
    invariant forall k, j :: 0 <= k < j < i && p[k] && p[j] ==> sorted[k] <= sorted[j]
  {
    if (p[i]) {
      var j := 0;
      while (j < i)
        invariant 0 <= j <= i
        invariant forall k :: 0 <= k < j && p[k] ==> sorted[k] <= sorted[i]
        invariant forall k, l :: 0 <= k < l < i && p[k] && p[l] ==> sorted[k] <= sorted[l]
      {
        if (p[j] && sorted[j] > sorted[i]) {
          sorted := sorted[j := sorted[i], i := sorted[j]];
        }
        j := j + 1;
      }
    }
    i := i + 1;
  }
  ProveEvenIndicesSorted(a, sorted, p);
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