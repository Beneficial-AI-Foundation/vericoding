function getSize(i: int, j:int) : int
{
  j - i + 1  
}

//IMPL 
method longestZero(a: array<int>) returns (sz:int, pos:int)  
  requires 1 <= a.Length
  ensures 0 <= sz <= a.Length
  ensures 0 <= pos < a.Length
  ensures pos + sz <= a.Length
  ensures forall i:int :: pos <= i < pos + sz ==> a[i] == 0
  ensures forall i,j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0
{
  sz := 0;
  pos := 0;
  var currentStart := 0;
  var currentSize := 0;
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= sz <= a.Length
    invariant 0 <= pos < a.Length
    invariant pos + sz <= a.Length
    invariant forall k :: pos <= k < pos + sz ==> a[k] == 0
    invariant 0 <= currentStart <= i
    invariant 0 <= currentSize <= i - currentStart
    invariant currentStart + currentSize <= i
    invariant forall k :: currentStart <= k < currentStart + currentSize ==> a[k] == 0
    /* code modified by LLM (iteration 4): Modified invariant to only consider processed elements */
    invariant forall p, q :: (0 <= p < q < i && getSize(p, q) > sz) ==> exists k :: p <= k <= q && a[k] != 0
    invariant if currentSize > 0 then (currentStart + currentSize == i && forall k :: currentStart <= k < i ==> a[k] == 0) else true
    invariant currentSize == 0 ==> (i > 0 ==> a[i-1] != 0)
  {
    if a[i] == 0 {
      if currentSize == 0 {
        currentStart := i;
      }
      currentSize := currentSize + 1;
      if currentSize > sz {
        /* code modified by LLM (iteration 4): Added proof that updating sz maintains invariant */
        var oldSz := sz;
        assert forall k :: currentStart <= k < currentStart + currentSize ==> a[k] == 0;
        assert currentStart + currentSize == i + 1;
        
        // Prove that the invariant will be maintained with new sz
        forall p, q | 0 <= p < q < i + 1 && getSize(p, q) > currentSize 
          ensures exists k :: p <= k <= q && a[k] != 0
        {
          if q <= i {
            // This follows from the old invariant since getSize(p, q) > currentSize > oldSz
            assert getSize(p, q) > oldSz;
            assert exists k :: p <= k <= q && a[k] != 0;
          }
        }
        
        sz := currentSize;
        pos := currentStart;
      }
    } else {
      /* code modified by LLM (iteration 4): Added proof for maintaining invariant when resetting */
      // When we encounter non-zero at position i, any segment ending at i has a non-zero element
      assert a[i] != 0;
      currentSize := 0;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 4): Final proof using loop invariant */
  forall p, q | 0 <= p < q < a.Length && getSize(p, q) > sz 
    ensures exists k :: p <= k <= q && a[k] != 0
  {
    assert 0 <= p < q < i && getSize(p, q) > sz;
    assert exists k :: p <= k <= q && a[k] != 0;
  }
}