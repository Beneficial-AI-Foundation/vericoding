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

//ATOM
predicate SwapFrame(a: array<int>, lo: int, hi: int)
  reads a
  requires 0 <= lo <= hi <= a.Length
{
  forall i :: 0 <= i < a.Length && (i < lo || i >= hi) ==> a[i] == old(a[i])
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
  if lo + 1 >= hi {
    /* code modified by LLM (iteration 2): Base case - array segment is trivially sorted */
    return;
  }
  
  /* code modified by LLM (iteration 2): Call partition to get pivot index */
  var p := Partition(a, lo, hi);
  
  /* code modified by LLM (iteration 2): Establish SplitPoint properties for recursive calls */
  assert SplitPoint(a, lo);
  assert SplitPoint(a, p);
  assert SplitPoint(a, p + 1);
  assert SplitPoint(a, hi);
  
  /* code modified by LLM (iteration 2): Recursively sort left partition */
  QuickSortAux(a, lo, p);
  
  /* code modified by LLM (iteration 2): Recursively sort right partition */
  QuickSortAux(a, p + 1, hi);
  
  /* code modified by LLM (iteration 2): Establish final sorting property */
  assert forall i,j :: lo <= i < j < hi ==> a[i] <= a[j] by {
    forall i, j | lo <= i < j < hi 
    ensures a[i] <= a[j]
    {
      if j < p {
        /* code modified by LLM (iteration 2): Both in left partition - sorted by first recursive call */
        assert lo <= i < j < p;
      } else if j == p {
        /* code modified by LLM (iteration 2): j is pivot, i < p */
        assert i < p;
        assert a[i] < a[p];  // From partition postcondition
      } else if i >= p + 1 {
        /* code modified by LLM (iteration 2): Both in right partition - sorted by second recursive call */
        assert p + 1 <= i < j < hi;
      } else if i == p {
        /* code modified by LLM (iteration 2): i is pivot, j > p */
        assert p < j;
        assert a[p] <= a[j];  // From partition postcondition
      } else {
        /* code modified by LLM (iteration 2): i < p < j case with transitivity */
        assert i < p < j;
        assert a[i] < a[p];   // From partition postcondition
        assert a[p] <= a[j];  // From partition postcondition
      }
    }
  }
  
  /* code modified by LLM (iteration 2): Establish SwapFrame property */
  assert SwapFrame(a, lo, hi);
  
  /* code modified by LLM (iteration 2): Establish SplitPoint properties */
  assert SplitPoint(a, lo);
  assert SplitPoint(a, hi);
}