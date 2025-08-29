// <vc-helpers>
// Helper function to check if an element is in a list
predicate InList(x: int, lst: seq<int>)
{
  exists i :: 0 <= i < |lst| && lst[i] == x
}

// Helper function to check if a list is sorted
predicate IsSorted(lst: seq<int>)
{
  forall i, j :: 0 <= i < j < |lst| ==> lst[i] <= lst[j]
}

// Helper function to check if a list has unique elements
predicate IsUnique(lst: seq<int>)
{
  forall i, j :: 0 <= i < j < |lst| ==> lst[i] != lst[j]
}

// Helper lemma to prove properties about multisets and sorted sequences
lemma MultisetAppend(a: seq<int>, b: seq<int>)
  ensures multiset(a + b) == multiset(a) + multiset(b)
{
}

// Helper method to sort a sequence
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures multiset(s) == multiset(sorted)
  ensures IsSorted(sorted)
{
  if |s| <= 1 {
    return s;
  }
  var mid := |s| / 2;
  var left := SortSeq(s[..mid]);
  var right := SortSeq(s[mid..]);
  sorted := Merge(left, right);
}

// Helper method to merge two sorted sequences
method Merge(left: seq<int>, right: seq<int>) returns (merged: seq<int>)
  requires IsSorted(left)
  requires IsSorted(right)
  ensures multiset(left) + multiset(right) == multiset(merged)
  ensures IsSorted(merged)
{
  merged := [];
  var i := 0;
  var j := 0;
  while i < |left| || j < |right|
    invariant 0 <= i <= |left|
    invariant 0 <= j <= |right|
    invariant IsSorted(merged)
    invariant multiset(merged) == multiset(left[..i]) + multiset(right[..j])
    decreases |left| - i + |right| - j
  {
    if i < |left| && (j >= |right| || left[i] <= right[j]) {
      merged := merged + [left[i]];
      i := i + 1;
    } else if j < |right| {
      merged := merged + [right[j]];
      j := j + 1;
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def common(l1: List[Int], l2: List[Int]) -> List[Int]
Return sorted unique common elements for two lists.
*/
// </vc-description>

// <vc-spec>
method Common(l1: seq<int>, l2: seq<int>) returns (result: seq<int>)
  ensures IsSorted(result)
  ensures IsUnique(result)
  ensures forall x :: x in result ==> InList(x, l1) && InList(x, l2)
  ensures forall x :: InList(x, l1) && InList(x, l2) ==> InList(x, result)
// </vc-spec>
// <vc-code>
{
  var common: seq<int> := [];
  var sorted_l1 := SortSeq(l1);
  var sorted_l2 := SortSeq(l2);
  var i := 0;
  var j := 0;
  while i < |sorted_l1| && j < |sorted_l2|
    invariant 0 <= i <= |sorted_l1|
    invariant 0 <= j <= |sorted_l2|
    invariant IsSorted(common)
    invariant IsUnique(common)
    invariant forall x :: x in common ==> InList(x, sorted_l1) && InList(x, sorted_l2)
    invariant forall x :: x in common ==> InList(x, l1) && InList(x, l2)
    invariant forall x :: (exists k :: 0 <= k < i && sorted_l1[k] == x) && (exists m :: 0 <= m < j && sorted_l2[m] == x) ==> InList(x, common)
    decreases |sorted_l1| - i + |sorted_l2| - j
  {
    if sorted_l1[i] == sorted_l2[j] {
      if !InList(sorted_l1[i], common) {
        common := common + [sorted_l1[i]];
      }
      i := i + 1;
      j := j + 1;
    } else if sorted_l1[i] < sorted_l2[j] {
      i := i + 1;
    } else {
      j := j + 1;
    }
  }
  result := common;
}
// </vc-code>
