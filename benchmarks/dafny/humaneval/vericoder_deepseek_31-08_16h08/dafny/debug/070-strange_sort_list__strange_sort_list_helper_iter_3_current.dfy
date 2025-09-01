

// <vc-helpers>
lemma MultisetProps(s: seq<int>, sorted: seq<int>, i: int, j: int)
  requires |s| == |sorted|
  requires multiset(s) == multiset(sorted)
  requires 0 <= i < |sorted|
  requires forall k :: 0 <= k < i ==> sorted[k] <= sorted[i]
  requires forall k :: i < k < |sorted| ==> sorted[i] <= sorted[k]
  requires 0 <= j <= |s|
  ensures multiset(s[0..j]) == multiset(sorted[0..j])
{
  // This lemma remains as it, but we need to ensure it's used correctly
}

lemma StrangeIndicesProperties(sorted: seq<int>, strange: seq<int>)
  requires |sorted| == |strange|
  requires forall i :: 0 <= i < |sorted| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
  requires forall i :: 0 <= i < |sorted| && i % 2 == 1 ==> strange[i] == sorted[|sorted| - (i - 1) / 2 - 1]
  ensures |sorted| == |strange|
{
}

lemma MultisetSubtraction(left: seq<int>, right: seq<int>)
  requires |left| == |right|
  requires multiset(left) == multiset(right)
  ensures forall j :: 0 <= j <= |left| ==> multiset(left[0..j]) == multiset(right[0..j])
{
  var j := 0;
  while j <= |left|
    invariant 0 <= j <= |left| + 1
    invariant forall k :: 0 <= k < j ==> multiset(left[0..k]) == multiset(right[0..k])
  {
    if j < |left| {
      // Need to show that if multisets are equal up to j, they're equal up to j+1
      // This requires additional properties about the sequences
    }
    j := j + 1;
  }
}

lemma MultisetPartitionHelper(sorted: seq<int>, left: int, right: int, count: int, strange: seq<int>)
  requires |sorted| >= 0
  requires 0 <= left <= |sorted|
  requires -1 <= right < |sorted|
  requires count >= 0
  requires |strange| == count
  requires count % 2 == 0 ==> left == count / 2 && right == |sorted| - count / 2 - 1
  requires count % 2 == 1 ==> left == (count + 1) / 2 && right == |sorted| - (count + 1) / 2 - 1
  requires multiset(strange) <= multiset(sorted)
  ensures multiset(strange) == multiset(sorted[0..left]) + multiset(sorted[right+1..|sorted|])
{
}

lemma LeftRightConsistency(left: int, right: int, count: int, n: int)
  requires n >= 0
  requires 0 <= count <= n
  requires count % 2 == 0 ==> left == count / 2 && right == n - count / 2 - 1
  requires count % 2 == 1 ==> left == (count + 1) / 2 && right == n - (count + 1) / 2 - 1
  ensures left + (n - right - 1) == count
{
}
// </vc-helpers>

// <vc-spec>
method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    // post-conditions-start
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := SortSeq(s);
  strange := [];
  var left := 0;
  var right := |s| - 1;
  var count := 0;
  
  ghost var left_index := 0;
  ghost var right_index := |s| - 1;
  
  while count < |s|
    invariant |strange| == count
    invariant 0 <= left <= |s|
    invariant -1 <= right < |s|
    invariant count % 2 == 0 ==> left == count / 2 && right == |s| - count / 2 - 1
    invariant count % 2 == 1 ==> left == (count + 1) / 2 && right == |s| - (count + 1) / 2 - 1
    invariant multiset(strange) == multiset(sorted[0..left]) + multiset(sorted[right+1..|s|])
    invariant left + (|s| - right - 1) == count
    invariant left_index == left
    invariant right_index == right
  {
    if count % 2 == 0 {
      assert left < |s|;
      strange := strange + [sorted[left]];
      left := left + 1;
    } else {
      assert right >= 0;
      strange := strange + [sorted[right]];
      right := right - 1;
    }
    count := count + 1;
    
    // Update ghost variables to help verification
    left_index := left;
    right_index := right;
  }
  
  // Post-loop assertions to help prove postconditions
  assert left + (|s| - right - 1) == |s|;
  assert left == (|s| + 1) / 2;  // When count is |s|, if |s| is odd, left = (|s| + 1)/2
  assert right == (|s| - 1) / 2 - 1 || (|s| % 2 == 0 && right == |s| / 2 - 1);
  assert multiset(strange) == multiset(sorted[0..left]) + multiset(sorted[right+1..|s|]) == multiset(sorted);
}
// </vc-code>

method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
    // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}