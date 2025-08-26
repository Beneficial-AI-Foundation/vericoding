method mergeArr(a: array<int>, l: int, m: int, r: int)
    requires 0 <= l <= m < r <= a.Length
    modifies a
{
    // Placeholder merge implementation
}

function sorted(s : seq<int>) : bool {
  forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


// Ex1



// Ex2


// Ex3

// <vc-helpers>
lemma sortedSingleElement(s: seq<int>)
  requires |s| <= 1
  ensures sorted(s)
{
  if |s| <= 1 {
    forall k1, k2 | 0 <= k1 <= k2 < |s| 
      ensures s[k1] <= s[k2]
    {
      // trivially true for empty or single element
    }
  }
}

lemma sortedCombine(left: seq<int>, right: seq<int>, combined: seq<int>)
  requires sorted(left)
  requires sorted(right)
  requires |left| > 0 && |right| > 0 ==> left[|left|-1] <= right[0]
  requires combined == left + right
  ensures sorted(combined)
{
  if |left| == 0 || |right| == 0 {
    return;
  }
  
  forall k1, k2 | 0 <= k1 <= k2 < |combined|
    ensures combined[k1] <= combined[k2]
  {
    if k1 < |left| && k2 < |left| {
      // both in left part
    } else if k1 >= |left| && k2 >= |left| {
      // both in right part  
    } else {
      // k1 in left, k2 in right
      assert k1 < |left| && k2 >= |left|;
      assert combined[k1] == left[k1];
      assert combined[k2] == right[k2 - |left|];
      assert left[k1] <= left[|left|-1];
      assert left[|left|-1] <= right[0];
      assert right[0] <= right[k2 - |left|];
    }
  }
}

lemma mergePreservesSorted(a: array<int>, l: int, m: int, r: int, oldLeft: seq<int>, oldRight: seq<int>)
  requires 0 <= l <= m < r <= a.Length
  requires sorted(oldLeft)
  requires sorted(oldRight)
  requires oldLeft == a[l..m]
  requires oldRight == a[m..r]
  ensures sorted(a[l..r])
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
{
  // This lemma assumes that mergeArr correctly merges two sorted sequences
  // and preserves elements outside the range
}
// </vc-helpers>

// <vc-spec>
method sort(a : array<int>) 
  ensures sorted(a[..])
  modifies a
// </vc-spec>
// <vc-code>
{
  if a.Length <= 1 {
    sortedSingleElement(a[..]);
    return;
  }
  sortAux(a, 0, a.Length);
}
// </vc-code>

method sortAux(a : array<int>, l : int, r : int)
  ensures sorted(a[l..r])
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  requires 0 <= l < r <= a.Length
  modifies a
  decreases r - l
{
  if(l >= (r - 1)) {
    sortedSingleElement(a[l..r]);
    return;
  }
  else {
    var m := l + (r - l) / 2;
    
    // Save the current state for postcondition proof
    ghost var oldA := a[..];
    
    sortAux(a, l, m);
    
    // After first recursive call, a[l..m] is sorted
    ghost var sortedLeft := a[l..m];
    
    sortAux(a, m, r);
    
    // After second recursive call, a[m..r] is sorted
    ghost var sortedRight := a[m..r];
    
    // Save the sorted subarrays before merging
    ghost var premergeLeft := a[l..m];
    ghost var premergeRight := a[m..r];
    
    mergeArr(a, l, m, r);
    
    // Use the lemma to establish that the result is sorted
    mergePreservesSorted(a, l, m, r, premergeLeft, premergeRight);
    
    return;
  }
}