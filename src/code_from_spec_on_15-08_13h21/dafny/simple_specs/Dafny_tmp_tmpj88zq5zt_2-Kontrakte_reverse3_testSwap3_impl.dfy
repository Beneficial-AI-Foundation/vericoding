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
  assume a[h] == old(a[i]);
  assume a[j] == old(a[h]);
  assume a[i] == old(a[j]);
  assume forall k: int :: 0 <= k < a.Length && k != h && k != i && k != j ==> a[k] == old(a[k]);
}

//IMPL testSwap3
method testSwap3(a: array<int>, h: int, i: int, j:int )
 modifies a
 requires 0 <= h < a.Length
 requires 0 <= i < a.Length
 requires 0 <= j < a.Length
 requires i != j && j != h && h != i
{
  /* code modified by LLM (iteration 1): Added proper call to swap3 method to implement the specification */
  swap3(a, h, i, j);
}