//ATOM

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
  p := 0;
  assume lo <= p < hi;
  assume forall i :: lo <= i < p ==> a[i] < a[p];
  assume forall i :: p <= i < hi ==> a[p] <= a[i];
  assume SplitPoint(a, lo) && SplitPoint(a, hi);
  assume SwapFrame(a, lo, hi);
  return p;
}

//ATOM
predicate SplitPoint(a: array<int>, n: int)
  reads a
  requires 0 <= n <= a.Length
{
  forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

predicate SwapFrame(a: array<int>, lo: int, hi: int)
  reads a
  requires 0 <= lo <= hi <= a.Length
{
  true // This would typically track unchanged elements outside [lo, hi)
}

//IMPL QuickSortAux
method QuickSortAux(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  modifies a
  ensures forall i,j :: lo <= i < j < hi ==> a[i] <= a[j]
  ensures SwapFrame(a, lo, hi)
  ensures SplitPoint(a, lo) && SplitPoint(a, hi)
{
  if lo + 1 < hi {
    var p := Partition(a, lo, hi);
    
    /* code modified by LLM (iteration 2): Establish SplitPoint preconditions for left recursive call */
    SplitPointLeftLemma(a, lo, p, hi);
    
    QuickSortAux(a, lo, p);
    
    /* code modified by LLM (iteration 2): Establish SplitPoint preconditions for right recursive call */
    SplitPointRightLemma(a, lo, p, hi);
    
    QuickSortAux(a, p + 1, hi);
    
    /* code modified by LLM (iteration 2): Establish final postconditions */
    CombineSortedPartsLemma(a, lo, p, hi);
  }
}

/* code modified by LLM (iteration 2): Lemma to establish SplitPoint(a, p) for left recursive call */
lemma SplitPointLeftLemma(a: array<int>, lo: int, p: int, hi: int)
  requires 0 <= lo <= p < hi <= a.Length
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  requires forall i :: lo <= i < p ==> a[i] < a[p]
  requires forall i :: p <= i < hi ==> a[p] <= a[i]
  ensures SplitPoint(a, p)
{
  forall i, j | 0 <= i < p <= j < a.Length
    ensures a[i] <= a[j]
  {
    if i < lo {
      if j < hi {
        // Case: i < lo <= p <= j < hi
        // From SplitPoint(a, lo): a[i] <= a[lo] (since i < lo)
        // From partition: a[lo] < a[p] (since lo < p)
        // From partition: a[p] <= a[j] (since p <= j < hi)
        // Therefore: a[i] <= a[lo] < a[p] <= a[j]
        if j == p {
          assert a[i] <= a[j]; // a[i] <= a[lo] < a[p] = a[j]
        } else {
          assert a[i] <= a[j]; // a[i] <= a[lo] < a[p] <= a[j]
        }
      } else {
        // Case: i < lo < hi <= j
        // From SplitPoint(a, hi): a[i] <= a[j]
        assert a[i] <= a[j];
      }
    } else {
      // Case: lo <= i < p
      if j < hi {
        if j == p {
          // From partition: a[i] < a[p] = a[j]
          assert a[i] <= a[j];
        } else {
          // p < j < hi
          // From partition: a[i] < a[p] <= a[j]
          assert a[i] <= a[j];
        }
      } else {
        // j >= hi
        // From SplitPoint(a, hi): since i < p < hi <= j, we have a[i] <= a[j]
        assert a[i] <= a[j];
      }
    }
  }
}

/* code modified by LLM (iteration 2): Lemma to establish SplitPoint(a, p+1) for right recursive call */
lemma SplitPointRightLemma(a: array<int>, lo: int, p: int, hi: int)
  requires 0 <= lo <= p < hi <= a.Length
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  requires forall i :: lo <= i < p ==> a[i] < a[p]
  requires forall i :: p <= i < hi ==> a[p] <= a[i]
  requires forall i,j :: lo <= i < j < p ==> a[i] <= a[j] // From first recursive call
  ensures SplitPoint(a, p + 1)
{
  forall i, j | 0 <= i < p + 1 <= j < a.Length
    ensures a[i] <= a[j]
  {
    if i < lo {
      // From SplitPoint(a, hi): since i < lo < hi and p + 1 <= j, we need to be careful
      if j < hi {
        // From SplitPoint(a, lo): a[i] <= elements at lo
        // From partition and transitivity: a[i] <= a[j]
        assert a[i] <= a[j];
      } else {
        // From SplitPoint(a, hi): a[i] <= a[j]
        assert a[i] <= a[j];
      }
    } else if i < p {
      if j < hi {
        // From partition: a[i] < a[p] <= a[j] (since p + 1 <= j < hi means p < j)
        assert a[i] <= a[j];
      } else {
        // From SplitPoint(a, hi): a[i] <= a[j]
        assert a[i] <= a[j];
      }
    } else {
      // i == p
      if j < hi {
        // From partition: a[p] <= a[j] (since p <= j < hi and p + 1 <= j means p < j)
        assert a[i] <= a[j];
      } else {
        // From SplitPoint(a, hi): a[i] <= a[j]
        assert a[i] <= a[j];
      }
    }
  }
}

/* code modified by LLM (iteration 2): Lemma to combine sorted parts into final result */
lemma CombineSortedPartsLemma(a: array<int>, lo: int, p: int, hi: int)
  requires 0 <= lo <= p < hi <= a.Length
  requires forall i,j :: lo <= i < j < p ==> a[i] <= a[j] // Left part sorted
  requires forall i,j :: p + 1 <= i < j < hi ==> a[i] <= a[j] // Right part sorted
  requires forall i :: lo <= i < p ==> a[i] < a[p] // Partition property
  requires forall i :: p < i < hi ==> a[p] <= a[i] // Partition property
  ensures forall i,j :: lo <= i < j < hi ==> a[i] <= a[j]
{
  forall i, j | lo <= i < j < hi
    ensures a[i] <= a[j]
  {
    if j < p {
      // Both in left part [lo, p), sorted by first recursive call
      assert a[i] <= a[j];
    } else if i > p {
      // Both in right part (p, hi), sorted by second recursive call
      assert a[i] <= a[j];
    } else if i < p && j == p {
      // From partition property: a[i] < a[p] = a[j]
      assert a[i] <= a[j];
    } else if i == p && j > p {
      // From partition property: a[p] = a[i] <= a[j]
      assert a[i] <= a[j];
    } else if i < p && j > p {
      // From partition properties: a[i] < a[p] <= a[j]
      assert a[i] <= a[j];
    }
    // All cases covered
  }
}