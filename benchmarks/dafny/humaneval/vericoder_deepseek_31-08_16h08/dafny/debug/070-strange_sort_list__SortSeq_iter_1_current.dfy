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
function sorted_by(s: seq<int>): bool
{
  if |s| <= 1 then true
  else s[0] <= s[1] && sorted_by(s[1..])
}

lemma SortedImpliesOrdered(s: seq<int>)
  requires sorted_by(s)
  ensures forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
{
}

lemma PermutationProperties(s1: seq<int>, s2: seq<int>)
  requires multiset(s1) == multiset(s2)
  requires sorted_by(s1) && sorted_by(s2)
  ensures s1 == s2
{
}

ghost method MergeSort(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  decreases |s|
{
  if |s| <= 1 {
    sorted := s;
  } else {
    var mid := |s| / 2;
    var left := MergeSort(s[..mid]);
    var right := MergeSort(s[mid..]);
    sorted := Merge(left, right);
  }
}

function Merge(left: seq<int>, right: seq<int>): seq<int>
  requires sorted_by(left) && sorted_by(right)
  ensures sorted_by(Merge(left, right))
  ensures multiset(Merge(left, right)) == multiset(left) + multiset(right)
  decreases |left| + |right|
{
  if |left| == 0 then right
  else if |right| == 0 then left
  else if left[0] <= right[0] then
    [left[0]] + Merge(left[1..], right)
  else
    [right[0]] + Merge(left, right[1..])
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
  var sorted := SortSeq(s);
  strange := [];
  var left := 0;
  var right := |s| - 1;
  var i := 0;
  
  while i < |s|
    invariant 0 <= left <= right + 1 <= |s|
    invariant |strange| == i
    invariant left + (|s| - right - 1) == i
    invariant forall j :: 0 <= j < i ==> 
      (j % 2 == 0 ==> strange[j] == sorted[j / 2]) &&
      (j % 2 == 1 ==> strange[j] == sorted[|s| - (j - 1) / 2 - 1])
  {
    if i % 2 == 0 {
      strange := strange + [sorted[left]];
      left := left + 1;
    } else {
      strange := strange + [sorted[right]];
      right := right - 1;
    }
    i := i + 1;
  }
}
// </vc-code>

