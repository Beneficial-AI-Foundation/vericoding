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
  var sorted := s;
  for i := 1 to |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |s|
    invariant multiset(sorted) == multiset(s)
    invariant forall j, k :: 0 <= j < k < i ==> sorted[j] <= sorted[k]
  {
    var j := i;
    while j > 0 && sorted[j-1] > sorted[j]
      invariant 0 <= j <= i
      invariant |sorted| == |s|
      invariant multiset(sorted) == multiset(s)
      invariant forall a, b :: 0 <= a < b < j ==> sorted[a] <= sorted[b]
      invariant forall a, b :: j <= a < b < i ==> sorted[a] <= sorted[b]
      invariant forall a, b :: 0 <= a < j && j <= b < i ==> sorted[a] <= sorted[b]
    {
      var temp := sorted[j];
      sorted := sorted[j := sorted[j-1]][j-1 := temp];
      j := j - 1;
    }
  }
  return sorted;
}
// </vc-code>

