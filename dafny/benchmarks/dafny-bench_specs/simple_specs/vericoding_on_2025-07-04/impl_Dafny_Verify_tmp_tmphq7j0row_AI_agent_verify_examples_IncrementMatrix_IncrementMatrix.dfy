//IMPL
method IncrementMatrix(a: array2<int>)
  modifies a
  ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
  var i := 0;
  /* code modified by LLM (iteration 1): Fixed outer loop invariants to properly track which rows have been processed */
  while i < a.Length0
    invariant 0 <= i <= a.Length0
    invariant forall r, c :: 0 <= r < i && 0 <= c < a.Length1 ==> a[r,c] == old(a[r,c]) + 1
    invariant forall r, c :: i <= r < a.Length0 && 0 <= c < a.Length1 ==> a[r,c] == old(a[r,c])
  {
    var j := 0;
    /* code modified by LLM (iteration 1): Fixed inner loop invariants to properly track column processing within current row */
    while j < a.Length1
      invariant 0 <= j <= a.Length1
      invariant forall r, c :: 0 <= r < i && 0 <= c < a.Length1 ==> a[r,c] == old(a[r,c]) + 1
      invariant forall c :: 0 <= c < j ==> a[i,c] == old(a[i,c]) + 1
      invariant forall c :: j <= c < a.Length1 ==> a[i,c] == old(a[i,c])
      invariant forall r, c :: i + 1 <= r < a.Length0 && 0 <= c < a.Length1 ==> a[r,c] == old(a[r,c])
    {
      a[i,j] := a[i,j] + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}