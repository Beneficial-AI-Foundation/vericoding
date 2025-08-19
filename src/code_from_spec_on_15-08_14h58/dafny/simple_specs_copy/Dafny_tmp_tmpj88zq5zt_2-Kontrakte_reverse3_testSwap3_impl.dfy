//ATOM
method swap3(a: array<int>, h: int, i: int, j: int)
 modifies a
 requires 0 <= h < a.Length
 requires 0 <= i < a.Length
 requires 0 <= j < a.Length
 requires i != j && j != h && h != i
 ensures a[h] == old(a[i])
 ensures a[j] == old(a[h])
 ensures a[i] == old(a[j])
 ensures forall k: int :: 0 <= k < a.Length && k != h && k != i && k != j ==> a[k] == old(a[k])
{
  /* code modified by LLM (iteration 1): implemented actual swap logic instead of assume statements */
  var temp_h := a[h];
  var temp_i := a[i];
  var temp_j := a[j];
  
  a[h] := temp_i;
  a[j] := temp_h;
  a[i] := temp_j;
}

//IMPL testSwap3
method testSwap3(a: array<int>, h: int, i: int, j:int )
 modifies a
 requires 0 <= h < a.Length
 requires 0 <= i < a.Length
 requires 0 <= j < a.Length
 requires i != j && j != h && h != i
{
  /* code modified by LLM (iteration 1): method call remains unchanged as it should verify correctly */
  swap3(a, h, i, j);
}