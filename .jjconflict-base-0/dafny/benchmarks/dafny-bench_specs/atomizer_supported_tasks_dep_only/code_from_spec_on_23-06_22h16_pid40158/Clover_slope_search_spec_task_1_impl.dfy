// IMPL SlopeSearch
method SlopeSearch(a: array2<int>, key: int) returns (m:int, n:int)
  requires forall i,j,j'::0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a[i,j]<=a[i,j']
  requires forall i,i',j::0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a[i,j]<=a[i',j]
  requires exists i,j :: 0<=i<a.Length0 && 0<=j<a.Length1 && a[i,j]==key
  ensures 0<=m<a.Length0 && 0<=n<a.Length1
  ensures a[m,n]==key
{
  var row := 0;
  var col := a.Length1 - 1;
  
  while row < a.Length0 && col >= 0
    invariant 0 <= row <= a.Length0
    invariant -1 <= col < a.Length1
    invariant exists i,j :: row <= i < a.Length0 && 0 <= j <= col && a[i,j] == key
  {
    if a[row, col] == key {
      m := row;
      n := col;
      return;
    } else if a[row, col] > key {
      col := col - 1;
    } else {
      row := row + 1;
    }
  }
  
  // This point should never be reached due to the precondition
  // but we need to assign values to satisfy the postcondition
  m := 0;
  n := 0;
}