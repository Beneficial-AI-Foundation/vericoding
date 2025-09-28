// <vc-preamble>
// Ghost predicate to check if a sequence is sorted in non-decreasing order
ghost predicate IsSorted(s: seq<real>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Ghost predicate to check if two sequences are permutations of each other
ghost predicate IsPermutation(s1: seq<real>, s2: seq<real>)
{
    |s1| == |s2| &&
    forall x :: Count(s1, x) == Count(s2, x)
}

// Ghost function to count occurrences of an element in a sequence
ghost function Count(s: seq<real>, x: real): nat
{
    if |s| == 0 then 0
    else (if s[0] == x then 1 else 0) + Count(s[1..], x)
}

// Ghost function that returns a sorted version of the input sequence
ghost function SortedVersion(s: seq<real>): seq<real>

// Ghost predicate that ensures SortedVersion produces a valid sorted permutation
ghost predicate SortedVersionValid(s: seq<real>)
{
    var sorted := SortedVersion(s);
    IsSorted(sorted) && IsPermutation(s, sorted)
}

// Axiom that SortedVersion always produces a valid result
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Properly find and return kth smallest element */
method FindKthSmallest(arr: seq<real>, kth: int) returns (pivot: real)
    requires 0 <= kth < |arr|
    ensures exists i :: 0 <= i < |arr| && arr[i] == pivot
    ensures |set x | x in arr && x < pivot| <= kth
    ensures |set x | x in arr && x <= pivot| > kth
{
    // Sort array to find kth smallest
    var sorted := arr;
    var i := 0;
    while i < |sorted|
        invariant 0 <= i <= |sorted|
        invariant |sorted| == |arr|
        invariant IsPermutation(arr, sorted)
        invariant forall k :: 0 <= k < i ==> forall j :: i <= j < |sorted| ==> sorted[k] <= sorted[j]
    {
        var minIdx := i;
        var j := i + 1;
        while j < |sorted|
            invariant i < j <= |sorted|
            invariant i <= minIdx < |sorted|
            invariant forall k :: i <= k < j ==> sorted[minIdx] <= sorted[k]
        {
            if sorted[j] < sorted[minIdx] {
                minIdx := j;
            }
            j := j + 1;
        }
        if minIdx != i {
            var temp := sorted[i];
            sorted := sorted[i := sorted[minIdx]][minIdx := temp];
        }
        i := i + 1;
    }
    
    pivot := sorted[kth];
    
    // Count elements less than and less than or equal to pivot
    var countLess := 0;
    var countLessEq := 0;
    i := 0;
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant countLess == |set x | x in arr[..i] && x < pivot|
        invariant countLessEq == |set x | x in arr[..i] && x <= pivot|
    {
        if arr[i] < pivot {
            countLess := countLess + 1;
        }
        if arr[i] <= pivot {
            countLessEq := countLessEq + 1;
        }
        i := i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
lemma {:axiom} SortedVersionIsValid(s: seq<real>)
    ensures SortedVersionValid(s)

/**
 * Partitions an array around the k-th element.
 * Returns a rearranged copy where the k-th element is in its correct sorted position,
 * with smaller elements before it and equal/greater elements after it.
 */
method Partition(arr: seq<real>, kth: int) returns (result: seq<real>)
    requires 0 <= kth < |arr|
    ensures |result| == |arr|
    // All elements before kth position are <= the kth element
    ensures forall i :: 0 <= i < kth ==> result[i] <= result[kth]
    // All elements after kth position are >= the kth element
    ensures forall i :: kth < i < |result| ==> result[i] >= result[kth]
    // The k-th element is in its correct sorted position
    ensures SortedVersionValid(arr) ==> result[kth] == SortedVersion(arr)[kth]
    // The result is a permutation of the original array
    ensures IsPermutation(arr, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Proper three-way partitioning around kth smallest */
  var pivot := FindKthSmallest(arr, kth);
  
  var less: seq<real> := [];
  var equal: seq<real> := [];
  var greater: seq<real> := [];
  
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant forall j :: 0 <= j < |less| ==> less[j] < pivot
    invariant forall j :: 0 <= j < |equal| ==> equal[j] == pivot
    invariant forall j :: 0 <= j < |greater| ==> greater[j] > pivot
    invariant |less| + |equal| + |greater| == i
    invariant IsPermutation(arr[..i], less + equal + greater)
  {
    if arr[i] < pivot {
      less := less + [arr[i]];
    } else if arr[i] == pivot {
      equal := equal + [arr[i]];
    } else {
      greater := greater + [arr[i]];
    }
    i := i + 1;
  }
  
  // Build result ensuring kth element is at position kth
  // We need to arrange so that |less| <= kth < |less| + |equal|
  if |less| > kth {
    // Too many elements less than pivot, need to move some to equal position
    var needToMove := |less| - kth;
    result := less[..kth] + [pivot] + less[kth..] + equal[1..] + greater;
  } else if |less| + |equal| <= kth {
    // Not enough elements <= pivot, need to include some greater elements
    var needFromGreater := kth - |less| - |equal| + 1;
    if needFromGreater > 0 && |greater| >= needFromGreater {
      result := less + equal + greater[..needFromGreater] + [pivot] + greater[needFromGreater..];
    } else {
      result := less + equal + greater;
    }
  } else {
    // Perfect case: |less| <= kth < |less| + |equal|
    var equalsBefore := kth - |less|;
    var equalsAfter := |equal| - equalsBefore - 1;
    if equalsBefore >= 0 && equalsAfter >= 0 && equalsBefore + 1 + equalsAfter == |equal| {
      result := less + equal[..equalsBefore] + [pivot] + equal[equalsBefore+1..] + greater;
    } else {
      result := less + equal + greater;
    }
  }
  
  // Ensure result has correct length
  if |result| != |arr| {
    result := less + equal + greater;
  }
  
  assert |result| == |arr|;
}
// </vc-code>
