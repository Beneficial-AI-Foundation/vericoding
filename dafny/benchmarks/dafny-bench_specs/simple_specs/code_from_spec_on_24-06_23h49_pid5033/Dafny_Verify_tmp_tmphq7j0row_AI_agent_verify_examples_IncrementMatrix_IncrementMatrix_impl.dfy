//IMPL IncrementMatrix
method IncrementMatrix(a: array2<int>)
  modifies a
  ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
  /* code modified by LLM (iteration 1): Fixed loop invariants to properly maintain the relationship between processed and unprocessed elements */
  var i := 0;
  while i < a.Length0
    invariant 0 <= i <= a.Length0
    invariant forall r, c :: 0 <= r < i && 0 <= c < a.Length1 ==> a[r,c] == old(a[r,c]) + 1
    invariant forall r, c :: i <= r < a.Length0 && 0 <= c < a.Length1 ==> a[r,c] == old(a[r,c])
  {
    var j := 0;
    while j < a.Length1
      invariant 0 <= j <= a.Length1
      invariant forall r, c :: 0 <= r < i && 0 <= c < a.Length1 ==> a[r,c] == old(a[r,c]) + 1
      invariant forall r, c :: i < r < a.Length0 && 0 <= c < a.Length1 ==> a[r,c] == old(a[r,c])
      invariant forall c :: 0 <= c < j ==> a[i,c] == old(a[i,c]) + 1
      invariant forall c :: j <= c < a.Length1 ==> a[i,c] == old(a[i,c])
    {
      a[i,j] := a[i,j] + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}