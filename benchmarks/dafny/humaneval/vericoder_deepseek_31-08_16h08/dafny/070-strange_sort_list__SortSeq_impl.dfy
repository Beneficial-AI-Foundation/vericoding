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
  if |s| > 1 {
    SortedImpliesOrdered(s[1..]);
  }
}

lemma PermutationProperties(s1: seq<int>, s2: seq<int>)
  requires multiset(s1) == multiset(s2)
  requires sorted_by(s1) && sorted_by(s2)
  ensures s1 == s2
{
  if |s1| == 0 {
    assert |s2| == 0;
  } else if |s1| == 1 {
    assert |s2| == 1 && s1[0] == s2[0];
  } else {
    var s1_tail := s1[1..];
    var s2_tail := s2[1..];
    assert multiset(s1_tail) == multiset(s2_tail);
    assert sorted_by(s1_tail) && sorted_by(s2_tail);
    PermutationProperties(s1_tail, s2_tail);
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
    var merged_tail := Merge(left[1..], right);
    [left[0]] + merged_tail
  else
    var merged_tail := Merge(left, right[1..]);
    [right[0]] + merged_tail
}
// </vc-helpers>
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
  if |s| == 0 {
    sorted := [];
  } else {
    var sortedTemp := s;
    // Sort the sequence by implementing a simple selection sort
    var i := 0;
    while i < |sortedTemp|
      invariant 0 <= i <= |sortedTemp|
      invariant forall k, l :: 0 <= k < l < i ==> sortedTemp[k] <= sortedTemp[l]
      invariant multiset(sortedTemp) == multiset(s)
      invariant |sortedTemp| == |s|
      decreases |sortedTemp| - i
    {
      var minIndex := i;
      var j := i + 1;
      while j < |sortedTemp|
        invariant i <= minIndex < |sortedTemp|
        invariant i < j <= |sortedTemp|
        invariant forall k :: i <= k < j ==> sortedTemp[minIndex] <= sortedTemp[k]
        invariant forall k, l :: 0 <= k < l < i ==> sortedTemp[k] <= sortedTemp[l]
        invariant multiset(sortedTemp) == multiset(s)
        invariant |sortedTemp| == |s|
        decreases |sortedTemp| - j
      {
        if sortedTemp[j] < sortedTemp[minIndex] {
          minIndex := j;
        }
        j := j + 1;
      }
      if minIndex != i {
        sortedTemp := sortedTemp[..i] + [sortedTemp[minIndex]] + sortedTemp[i+1..minIndex] + [sortedTemp[i]] + sortedTemp[minIndex+1..];
      }
      i := i + 1;
    }
    sorted := sortedTemp;
  }
}
// </vc-code>

