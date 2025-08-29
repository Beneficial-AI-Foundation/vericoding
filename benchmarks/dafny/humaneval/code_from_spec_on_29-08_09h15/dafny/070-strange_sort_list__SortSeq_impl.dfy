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
lemma SortedProperty(s: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
{
}

lemma MultisetPreservation(s: seq<int>, sorted: seq<int>)
  requires multiset(s) == multiset(sorted)
  ensures |s| == |sorted|
{
}

lemma QuicksortCorrectness(s: seq<int>, pivot: int, smaller: seq<int>, equal: seq<int>, greater: seq<int>, sorted_smaller: seq<int>, sorted_greater: seq<int>)
  requires multiset(s) == multiset(smaller) + multiset(equal) + multiset(greater)
  requires forall x :: x in smaller ==> x < pivot
  requires forall x :: x in equal ==> x == pivot
  requires forall x :: x in greater ==> x > pivot
  requires forall i, j :: 0 <= i < j < |sorted_smaller| ==> sorted_smaller[i] <= sorted_smaller[j]
  requires forall i, j :: 0 <= i < j < |sorted_greater| ==> sorted_greater[i] <= sorted_greater[j]
  requires multiset(smaller) == multiset(sorted_smaller)
  requires multiset(greater) == multiset(sorted_greater)
  ensures var result := sorted_smaller + equal + sorted_greater;
          forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
{
  var result := sorted_smaller + equal + sorted_greater;
  forall i, j | 0 <= i < j < |result|
    ensures result[i] <= result[j]
  {
    if j < |sorted_smaller| {
      assert result[i] == sorted_smaller[i] && result[j] == sorted_smaller[j];
    } else if i >= |sorted_smaller| + |equal| {
      assert result[i] == sorted_greater[i - |sorted_smaller| - |equal|];
      assert result[j] == sorted_greater[j - |sorted_smaller| - |equal|];
    } else if i < |sorted_smaller| && j >= |sorted_smaller| + |equal| {
      assert result[i] in multiset(sorted_smaller) && result[j] in multiset(sorted_greater);
      assert result[i] in smaller && result[j] in greater;
      assert result[i] < pivot && result[j] > pivot;
    } else if i < |sorted_smaller| && |sorted_smaller| <= j < |sorted_smaller| + |equal| {
      assert result[i] in multiset(sorted_smaller) && result[j] in equal;
      assert result[i] in smaller && result[j] == pivot;
      assert result[i] < pivot;
    } else if |sorted_smaller| <= i < |sorted_smaller| + |equal| && j >= |sorted_smaller| + |equal| {
      assert result[i] in equal && result[j] in multiset(sorted_greater);
      assert result[i] == pivot && result[j] in greater;
      assert result[j] > pivot;
    }
  }
}

lemma MultisetSliceExtension(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures multiset(s[0..i]) + multiset([s[i]]) == multiset(s[0..i+1])
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method SortSeq(s: seq<int>) returns (sorted: seq<int>)
Sort elements. Ensures: the result is sorted according to the ordering relation; returns the correct size/count; returns a sorted permutation of the input.
*/
// </vc-description>

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
    return [];
  }
  
  if |s| == 1 {
    return s;
  }
  
  var pivot := s[0];
  var smaller := [];
  var equal := [];
  var greater := [];
  
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant forall x :: x in smaller ==> x < pivot
    invariant forall x :: x in equal ==> x == pivot
    invariant forall x :: x in greater ==> x > pivot
    invariant multiset(s[0..i]) == multiset(smaller) + multiset(equal) + multiset(greater)
  {
    if s[i] < pivot {
      smaller := smaller + [s[i]];
    } else if s[i] == pivot {
      equal := equal + [s[i]];
    } else {
      greater := greater + [s[i]];
    }
  }
  
  assert s[0..0] == [];
  assert s[0..|s|] == s;
  assert multiset(s) == multiset(smaller) + multiset(equal) + multiset(greater);
  assert pivot in equal;
  assert |equal| >= 1;
  
  var sorted_smaller: seq<int>;
  var sorted_greater: seq<int>;
  
  if |smaller| > 0 {
    sorted_smaller := SortSeq(smaller);
  } else {
    sorted_smaller := [];
  }
  
  if |greater| > 0 {
    sorted_greater := SortSeq(greater);
  } else {
    sorted_greater := [];
  }
  
  sorted := sorted_smaller + equal + sorted_greater;
  
  QuicksortCorrectness(s, pivot, smaller, equal, greater, sorted_smaller, sorted_greater);
}
// </vc-code>

