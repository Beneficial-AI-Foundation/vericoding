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
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma LemmaSortSeqProperties(s: seq<int>, sorted: seq<int>)
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  requires |sorted| == |s|
  requires multiset(s) == multiset(sorted)
{
}

function GetElement(sorted: seq<int>, s: seq<int>, i: int): int
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  requires |sorted| == |s|
  requires multiset(s) == multiset(sorted)
  requires 0 <= i < |s|
{
  if i % 2 == 0 then
    sorted[i / 2]
  else
    sorted[|s| - (i - 1) / 2 - 1]
}

lemma LemmaGetElementProperties(s: seq<int>, sorted: seq<int>, i: int)
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  requires |sorted| == |s|
  requires multiset(s) == multiset(sorted)
  requires 0 <= i < |s|
  ensures GetElement(sorted, s, i) == 
    if i % 2 == 0 then sorted[i / 2] else sorted[|s| - (i - 1) / 2 - 1]
{
  if i % 2 == 0 {
    assert GetElement(sorted, s, i) == sorted[i / 2];
  } else {
    assert GetElement(sorted, s, i) == sorted[|s| - (i - 1) / 2 - 1];
  }
}
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
  var sorted := [];
  for i := 0 to |s| - 1
    invariant |sorted| == i
    invariant forall k, l :: 0 <= k < l < |sorted| ==> sorted[k] <= sorted[l]
    invariant multiset(s[0..i]) == multiset(sorted)
  {
    var j := 0;
    while j < |sorted| && sorted[j] <= s[i]
      invariant 0 <= j <= |sorted|
      invariant forall k :: 0 <= k < j ==> sorted[k] <= s[i]
    {
      j := j + 1;
    }
    sorted := sorted[..j] + [s[i]] + sorted[j..];
  }
  return sorted;
}
// </vc-code>

