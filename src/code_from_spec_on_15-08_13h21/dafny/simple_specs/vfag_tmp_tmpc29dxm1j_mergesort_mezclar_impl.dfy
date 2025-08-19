//IMPL 

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
  
  while i < m && j < f
    invariant c <= i <= m
    invariant m <= j <= f
    invariant 0 <= k <= temp.Length
    invariant k == (i - c) + (j - m)
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
  
  /* code modified by LLM (iteration 1): Fixed loop invariant - j may not equal f when entering this loop */
  while i < m
    invariant c <= i <= m
    invariant m <= j <= f
    invariant 0 <= k <= temp.Length
    invariant k == (i - c) + (j - m)
  {
    temp[k] := V[i];
    i := i + 1;
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 1): Fixed loop invariant - i may not equal m when entering this loop */
  while j < f
    invariant c <= i <= m
    invariant m <= j <= f
    invariant 0 <= k <= temp.Length
    invariant k == (i - c) + (j - m)
  {
    temp[k] := V[j];
    j := j + 1;
    k := k + 1;
  }
  
  k := 0;
  i := c;
  while i < f
    invariant c <= i <= f
    invariant 0 <= k <= temp.Length
    invariant k == i - c
  {
    V[i] := temp[k];
    i := i + 1;
    k := k + 1;
  }
}