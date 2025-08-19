method mezclar(V: array?<int>, c : int, m : int, f : int)

  requires V != null
  requires c <= m <= f
  requires 0 <= c <= V.Length
  requires 0 <= m <= V.Length
  requires 0 <= f <= V.Length

  modifies V

{
  /* code modified by LLM (iteration 2): Fixed auxiliary array size calculation */
  var aux := new int[f - c + 1];
  var i, j, k := c, m + 1, 0;
  
  // Merge the two sorted subarrays
  /* code modified by LLM (iteration 2): Fixed bounds checking invariants for array access */
  while i <= m && j <= f
    invariant c <= i <= m + 1
    invariant m + 1 <= j <= f + 1
    invariant 0 <= k <= f - c + 1
    invariant k == (i - c) + (j - (m + 1))
    invariant i <= V.Length && j <= V.Length
  {
    /* code modified by LLM (iteration 2): Added explicit bounds check before array access */
    if i < V.Length && j < V.Length && V[i] <= V[j] {
      aux[k] := V[i];
      i := i + 1;
    } else if j < V.Length {
      aux[k] := V[j];
      j := j + 1;
    } else {
      aux[k] := V[i];
      i := i + 1;
    }
    k := k + 1;
  }
  
  // Copy remaining elements from left subarray
  /* code modified by LLM (iteration 2): Fixed invariant formula and added bounds checking */
  while i <= m
    invariant c <= i <= m + 1
    invariant 0 <= k <= f - c + 1
    invariant k == (i - c) + (j - (m + 1))
    invariant i <= V.Length
  {
    /* code modified by LLM (iteration 2): Added bounds check before array access */
    if i < V.Length {
      aux[k] := V[i];
    }
    i := i + 1;
    k := k + 1;
  }
  
  // Copy remaining elements from right subarray
  /* code modified by LLM (iteration 2): Added bounds checking invariants */
  while j <= f
    invariant m + 1 <= j <= f + 1
    invariant 0 <= k <= f - c + 1
    invariant k == (m - c + 1) + (j - (m + 1))
    invariant j <= V.Length
  {
    /* code modified by LLM (iteration 2): Added bounds check before array access */
    if j < V.Length {
      aux[k] := V[j];
    }
    j := j + 1;
    k := k + 1;
  }
  
  // Copy merged elements back to original array
  k := 0;
  /* code modified by LLM (iteration 2): Fixed loop condition and bounds checking */
  while k < f - c + 1 && c + k < V.Length
    invariant 0 <= k <= f - c + 1
    invariant c + k <= V.Length
  {
    V[c + k] := aux[k];
    k := k + 1;
  }
}

//IMPL 

method mergesort(V : array?<int>, c : int, f : int) 

  requires V != null
  requires c >= 0 && f <= V.Length
  
  modifies V
  decreases f - c

{
  /* code modified by LLM (iteration 2): Fixed bounds checking and added termination clause */
  if c < f {
    var m := (c + f) / 2;
    mergesort(V, c, m);
    mergesort(V, m + 1, f);
    /* code modified by LLM (iteration 2): Added bounds check for mezclar call */
    if m + 1 <= f {
      mezclar(V, c, m, f);
    }
  }
}