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
method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var cur := s;
  var res : seq<int> := [];
  // invariants: number of elements preserved, multiset preserved, res sorted,
  // and every element of res <= every element of cur
  while |cur| > 0
    invariant |res| + |cur| == |s|
    invariant multiset(res) + multiset(cur) == multiset(s)
    invariant forall i, j :: 0 <= i < j < |res| ==> res[i] <= res[j]
    invariant forall x, y :: x in res && y in cur ==> x <= y
    decreases |cur|
  {
    // find minimal element index in cur
    var minIdx := 0;
    var i := 1;
    while i < |cur|
      invariant 0 <= minIdx < |cur|
      invariant 0 <= i <= |cur|
      invariant forall k :: 0 <= k < i ==> cur[minIdx] <= cur[k]
      decreases |cur| - i
    {
      if cur[i] < cur[minIdx] {
        minIdx := i;
      }
      i := i + 1;
    }
    var m := cur[minIdx];
    var rest := cur[..minIdx] + cur[minIdx+1..];
    // update res and cur
    res := res + [m];
    cur := rest;
    // Now prove the invariants hold for the next iteration:
    // - length: obvious from construction
    // - multiset: multiset(res + [m]) + multiset(rest) == multiset(res) + {m} + (multiset(cur) - {m}) == multiset(res) + multiset(cur) == multiset(s)
    // - ordering of res: previous res elements <= every element of old cur, in particular <= m; and m <= every element of rest because m was minimal in old cur
    //   hence res remains sorted and every element of res <= every element of new cur
  }
  sorted := res;
}
// </vc-code>

