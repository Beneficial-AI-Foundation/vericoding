method swap3(a: array<int>, h: int, i: int, j: int)
 modifies a
 requires 0 <= h < a.Length
 requires 0 <= i < a.Length
 requires 0 <= j < a.Length
 requires i != j && j != h && h != i
 ensures a[h] == old(a[i])
 ensures a[j] == old(a[h])
 ensures a[i] == old(a[j])
 /* code modified by LLM (iteration 1): removed semicolon after ensures clause to fix deprecated style warning */
 ensures forall k: int :: 0 <= k < a.Length && k != h && k != i && k != j ==> a[k] == old(a[k])
{
    var temp_h := a[h];
    var temp_i := a[i];
    var temp_j := a[j];
    
    a[h] := temp_i;
    a[j] := temp_h;
    a[i] := temp_j;
}