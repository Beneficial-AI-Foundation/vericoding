method swap(a: array<int>, i: nat, j: nat)
  modifies a
  /* code modified by LLM (iteration 1): removed redundant null check since array<int> is non-null type */
  requires a.Length > 0 && i < a.Length && j < a.Length
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}