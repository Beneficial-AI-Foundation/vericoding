//IMPL
//Problem01
//a)
method swap(a: array<int>, i: nat, j: nat)
  modifies a
  /* code modified by LLM (iteration 2): removed invalid text at start of file that was causing parse error */
  requires a.Length > 0 && i < a.Length && j < a.Length
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}