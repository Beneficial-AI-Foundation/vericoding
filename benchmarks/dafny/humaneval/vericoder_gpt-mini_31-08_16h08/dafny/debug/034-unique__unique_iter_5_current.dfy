method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function SeqToSet(s: seq<int>): set<int> {
  set x | exists i :: 0 <= i < |s| && s[i] == x
}
// </vc-helpers>

// <vc-spec>
method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var tmp: seq<int> := [];
  var seen: set<int> := {};
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall x :: x in tmp[..] <==> exists k :: 0 <= k < i && s[k] == x
    invariant forall p, q :: 0 <= p < q < |tmp| ==> tmp[p] != tmp[q]
    invariant seen == SeqToSet(tmp)
    decreases |s| - i
  {
    var x := s[i];
    if !(x in seen) {
      tmp := tmp + [x];
      seen := seen + {x};
    }
    i := i + 1;
  }

  var res: seq<int> := [];
  var k := 0;
  while k < |tmp|
    invariant 0 <= k <= |tmp|
    invariant forall p, q :: 0 <= p < q < |res| ==> res[p] < res[q]
    invariant forall x :: x in res[..] <==> exists t :: 0 <= t < k && tmp[t] == x
    invariant forall p, q :: 0 <= p < q < |tmp| ==> tmp[p] != tmp[q]
    decreases |tmp| - k
  {
    var x := tmp[k];
    var pos := 0;
    while pos < |res| && res[pos] < x
      invariant 0 <= pos <= |res|
      invariant forall t :: 0 <= t < pos ==> res[t] < x
      decreases |res| - pos
    {
      pos := pos + 1;
    }
    // If x is already present at pos, skip insertion; otherwise insert to keep strict ordering.
    if !(pos < |res| && res[pos] == x) {
      res := res[..pos] + [x] + res[pos..];
    }
    k := k + 1;
  }

  result := res;
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}