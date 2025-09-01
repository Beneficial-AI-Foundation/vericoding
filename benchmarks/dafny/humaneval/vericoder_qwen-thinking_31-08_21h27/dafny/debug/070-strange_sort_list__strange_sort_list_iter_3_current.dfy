method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    // post-conditions-start
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
var sorted := SortSeq(s);
var strange := new int[|s|];
for i := 0 to |s| - 1 {
  invariant forall k : nat | 0 <= k < i
      (if k % 2 == 0 then strange[k] == sorted[k / 2] else strange[k] == sorted[|s| - (k-1)/2 - 1])
  if i % 2 == 0 {
    strange[i] := sorted[i / 2];
  } else {
    strange[i] := sorted[|s| - (i - 1) / 2 - 1];
  }
}
return (sorted, strange);
// </vc-helpers>

// <vc-spec>
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
    // post-conditions-end
// </vc-spec>
// <vc-code>
var sorted, strange := strange_sort_list_helper(s);
return strange;
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