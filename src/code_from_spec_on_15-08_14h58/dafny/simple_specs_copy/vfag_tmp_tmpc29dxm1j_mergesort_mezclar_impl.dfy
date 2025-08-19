method mezclar(V: array?<int>, c : int, m : int, f : int)

  requires V != null
  requires c <= m <= f
  requires 0 <= c <= V.Length
  requires 0 <= m <= V.Length
  requires 0 <= f <= V.Length

  modifies V

{
  if c >= f {
    return;
  }
  
  var temp := new int[f - c];
  var i := c;
  var j := m;
  var k := 0;
  
  // Merge the two subarrays V[c..m) and V[m..f)
  while i < m && j < f
    invariant c <= i <= m
    invariant m <= j <= f
    invariant k == (i - c) + (j - m)
    invariant 0 <= k <= temp.Length
  {
    if V[i] <= V[j] {
      temp[k] := V[i];
      i := i + 1;
    } else {
      temp[k] := V[j];
      j := j + 1;
    }
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 1): Added assertions to establish the correct invariant for the second loop */
  assert k == (i - c) + (j - m);
  assert !(i < m && j < f);
  assert i >= m || j >= f;
  
  // Copy remaining elements from left subarray
  while i < m
    invariant c <= i <= m
    invariant j == f  // j must equal f when we enter this loop
    invariant k == (i - c) + (j - m)
    invariant 0 <= k <= temp.Length
  {
    temp[k] := V[i];
    i := i + 1;
    k := k + 1;
  }
  
  // Copy remaining elements from right subarray  
  while j < f
    invariant m <= j <= f
    invariant i == m  // i must equal m when we enter this loop
    invariant k == (i - c) + (j - m)
    invariant 0 <= k <= temp.Length
  {
    temp[k] := V[j];
    j := j + 1;
    k := k + 1;
  }
  
  // Copy merged elements back to original array
  k := 0;
  i := c;
  while i < f
    invariant c <= i <= f
    invariant k == i - c
    invariant 0 <= k <= temp.Length
  {
    V[i] := temp[k];
    i := i + 1;
    k := k + 1;
  }
}