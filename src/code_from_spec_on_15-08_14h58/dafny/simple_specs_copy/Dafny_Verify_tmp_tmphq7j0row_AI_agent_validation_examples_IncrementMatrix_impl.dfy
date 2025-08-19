function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}

//ATOM
method Cube(n: nat) returns (c: nat) 
  ensures c == n * n * n
{
  c := n * n * n;
}

//ATOM
method Max(a: array<nat>) returns (m: int)
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
  if a.Length == 0 {
    m := 0;
  } else {
    m := a[0];
    var i := 1;
    while i < a.Length
      invariant 1 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> a[k] <= m
      invariant exists k :: 0 <= k < i && m == a[k]
    {
      if a[i] > m {
        m := a[i];
      }
      i := i + 1;
    }
  }
}

//IMPL IncrementMatrix
method IncrementMatrix(a: array2<int>)
  modifies a
  ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
  /* code modified by LLM (iteration 1): Added proper loop invariants to track array modifications */
  var row := 0;
  while row < a.Length0
    invariant 0 <= row <= a.Length0
    invariant forall i, j :: 0 <= i < row && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
    invariant forall i, j :: row <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j])
  {
    var col := 0;
    while col < a.Length1
      invariant 0 <= col <= a.Length1
      invariant forall i, j :: 0 <= i < row && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
      invariant forall j :: 0 <= j < col ==> a[row,j] == old(a[row,j]) + 1
      invariant forall j :: col <= j < a.Length1 ==> a[row,j] == old(a[row,j])
      invariant forall i, j :: row < i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j])
    {
      a[row,col] := a[row,col] + 1;
      col := col + 1;
    }
    row := row + 1;
  }
}