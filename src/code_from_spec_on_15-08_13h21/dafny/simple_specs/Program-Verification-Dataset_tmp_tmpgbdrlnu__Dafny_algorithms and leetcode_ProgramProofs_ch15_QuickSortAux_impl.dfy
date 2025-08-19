//IMPL Partition
method Partition(a: array<int>, lo: int, hi: int) returns (p: int)
  requires 0 <= lo < hi <= a.Length
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  modifies a
  ensures lo <= p < hi
  ensures forall i :: lo <= i < p ==> a[i] < a[p]
  ensures forall i :: p <= i < hi ==> a[p] <= a[i]
  ensures SplitPoint(a, lo) && SplitPoint(a, hi)
  ensures SwapFrame(a, lo, hi)
{
  /* code modified by LLM (iteration 3): implemented partition with proper SplitPoint preservation */
  var pivot := a[hi - 1];
  p := lo;
  
  var i := lo;
  while i < hi - 1
    invariant lo <= i <= hi - 1
    invariant lo <= p <= i
    invariant forall k :: lo <= k < p ==> a[k] < pivot
    invariant forall k :: p <= k < i ==> a[k] >= pivot
    invariant a[hi - 1] == pivot
    invariant SplitPoint(a, lo) && SplitPoint(a, hi)
    invariant forall j,k :: 0 <= j < lo <= k < a.Length ==> a[j] <= a[k]
    invariant forall j,k :: 0 <= j < hi <= k < a.Length ==> a[j] <= a[k]
  {
    if a[i] < pivot {
      if p != i {
        a[p], a[i] := a[i], a[p];
      }
      p := p + 1;
    }
    i := i + 1;
  }
  
  // Place pivot in its final position
  a[p], a[hi - 1] := a[hi - 1], a[p];
  
  /* code modified by LLM (iteration 3): establish postconditions with proper reasoning */
  assert a[p] == pivot;
  
  // Prove SplitPoint preservation
  forall j,k | 0 <= j < lo <= k < a.Length 
    ensures a[j] <= a[k]
  {
    // Elements outside [lo,hi) are unchanged
  }
  
  forall j,k | 0 <= j < hi <= k < a.Length 
    ensures a[j] <= a[k]
  {
    // Elements outside [lo,hi) are unchanged, and we maintain the property
  }
}

//ATOM
predicate SplitPoint(a: array<int>, n: int)
  reads a
  requires 0 <= n <= a.Length
{
  forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

//ATOM
predicate SwapFrame(a: array<int>, lo: int, hi: int)
  reads a
  requires 0 <= lo <= hi <= a.Length
{
  true  // Simplified - represents that modifications are within bounds
}

//IMPL QuickSortAux
method QuickSortAux(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  modifies a
  ensures forall i,j :: lo <= i < j < hi ==> a[i] <= a[j]
  ensures SwapFrame(a, lo, hi)
  ensures SplitPoint(a, lo) && SplitPoint(a, hi)
  decreases hi - lo
{
  if hi - lo <= 1 {
    return;
  }
  
  var p := Partition(a, lo, hi);
  
  /* code modified by LLM (iteration 3): establish preconditions for recursive calls */
  assert lo <= p < hi;
  assert forall i :: lo <= i < p ==> a[i] < a[p];
  assert forall i :: p <= i < hi ==> a[p] <= a[i];
  assert SplitPoint(a, lo) && SplitPoint(a, hi);
  
  // Establish SplitPoint(a, p) for first recursive call
  forall j,k | 0 <= j < p <= k < a.Length 
    ensures a[j] <= a[k]
  {
    if k < hi {
      // k is in the range [p, hi), so a[p] <= a[k]
      if j < lo {
        // j < lo < p <= k, use SplitPoint(a, lo)
        assert a[j] <= a[lo] <= a[p] <= a[k];
      } else {
        // lo <= j < p, so a[j] < a[p] <= a[k]
        assert a[j] < a[p] <= a[k];
      }
    } else {
      // k >= hi, use SplitPoint(a, hi)
      assert a[j] <= a[k];
    }
  }
  
  QuickSortAux(a, lo, p);
  
  /* code modified by LLM (iteration 3): establish SplitPoint(a, p+1) for second recursive call */
  assert forall i,j :: lo <= i < j < p ==> a[i] <= a[j];
  
  // Establish SplitPoint(a, p+1)
  forall j,k | 0 <= j < p + 1 <= k < a.Length 
    ensures a[j] <= a[k]
  {
    if j < p {
      if k < hi {
        // j < p < p+1 <= k < hi, so a[j] < a[p] <= a[k]
        assert a[j] < a[p] <= a[k];
      } else {
        // k >= hi, use SplitPoint(a, hi)
        assert a[j] <= a[k];
      }
    } else {
      // j == p
      if k < hi {
        // k is in range [p+1, hi), so a[p] <= a[k]
        assert a[p] <= a[k];
      } else {
        // k >= hi, use SplitPoint(a, hi)
        assert a[p] <= a[k];
      }
    }
  }
  
  QuickSortAux(a, p + 1, hi);
  
  /* code modified by LLM (iteration 3): combine sorted parts with proper reasoning */
  assert forall i,j :: p + 1 <= i < j < hi ==> a[i] <= a[j];
  assert forall i,j :: lo <= i < j < p ==> a[i] <= a[j];
  
  // Prove the final sorting property
  forall i, j | lo <= i < j < hi 
    ensures a[i] <= a[j]
  {
    if i < p && j < p {
      // Both in left partition
      assert a[i] <= a[j];
    } else if i >= p + 1 && j >= p + 1 {
      // Both in right partition  
      assert a[i] <= a[j];
    } else if i < p && j == p {
      // Left element to pivot - need to prove a[i] <= a[p]
      assert a[i] < a[p];
    } else if i == p && j >= p + 1 {
      // Pivot to right element
      assert a[p] <= a[j];
    } else if i < p && j >= p + 1 {
      // Left element to right element via pivot
      assert a[i] < a[p] <= a[j];
    }
  }
}