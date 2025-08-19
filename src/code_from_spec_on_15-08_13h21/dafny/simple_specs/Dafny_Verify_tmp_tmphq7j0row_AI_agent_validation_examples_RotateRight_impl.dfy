method Cube(n: nat) returns (c: nat) 
  ensures c == n * n * n
{
  /* code modified by LLM (iteration 1): Fixed implementation to compute cube correctly */
  c := n * n * n;
}

//ATOM
method CopyMatrix(src: array2<int>, dst: array2<int>)
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
  ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{
  /* code modified by LLM (iteration 4): Fixed loop invariant by ensuring src is not modified */
  var i := 0;
  while i < src.Length0
    invariant 0 <= i <= src.Length0
    invariant forall r, c :: 0 <= r < i && 0 <= c < src.Length1 ==> dst[r,c] == old(src[r,c])
  {
    var j := 0;
    while j < src.Length1
      invariant 0 <= j <= src.Length1
      invariant forall r, c :: 0 <= r < i && 0 <= c < src.Length1 ==> dst[r,c] == old(src[r,c])
      invariant forall c :: 0 <= c < j ==> dst[i,c] == src[i,c]
    {
      dst[i,j] := src[i,j];
      j := j + 1;
    }
    i := i + 1;
  }
}

//ATOM
method RotateLeft(a: array<int>)
  requires a.Length > 0
  modifies a
  ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]) 
  ensures a[a.Length -1] == old(a[0])
{
  /* code modified by LLM (iteration 1): Implemented proper left rotation */
  if a.Length == 1 { return; }
  
  var temp := a[0];
  var i := 0;
  
  while i < a.Length - 1
    invariant 0 <= i <= a.Length - 1
    invariant temp == old(a[0])
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[j+1])
    invariant forall j :: i < j < a.Length ==> a[j] == old(a[j])
  {
    a[i] := a[i+1];
    i := i + 1;
  }
  
  a[a.Length-1] := temp;
}

//ATOM
method IncrementMatrix(a: array2<int>)
  modifies a
  ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
  /* code modified by LLM (iteration 1): Implemented proper matrix increment with nested loops */
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
      invariant forall c :: 0 <= c < j ==> a[i,c] == old(a[i,c]) + 1
      invariant forall c :: j <= c < a.Length1 ==> a[i,c] == old(a[i,c])
      invariant forall r, c :: i < r < a.Length0 && 0 <= c < a.Length1 ==> a[r,c] == old(a[r,c])
    {
      a[i,j] := a[i,j] + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}

//ATOM
method Max(a: array<nat>) returns (m: int)
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
  /* code modified by LLM (iteration 1): Implemented proper maximum finding algorithm */
  if a.Length == 0 {
    m := 0;
    return;
  }
  
  m := a[0];
  var i := 1;
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] <= m
    invariant exists j :: 0 <= j < i && m == a[j]
  {
    if a[i] > m {
      m := a[i];
    }
    i := i + 1;
  }
}

//ATOM
function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}

//ATOM
method DoubleArray(src: array<int>, dst: array<int>)
  requires src.Length == dst.Length
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{
  /* code modified by LLM (iteration 2): Fixed loop invariant to properly reference old values */
  var i := 0;
  while i < src.Length
    invariant 0 <= i <= src.Length
    invariant forall j :: 0 <= j < i ==> dst[j] == 2 * old(src[j])
    invariant forall j :: i <= j < src.Length ==> dst[j] == old(dst[j])
  {
    dst[i] := 2 * src[i];
    i := i + 1;
  }
}

//IMPL RotateRight
method RotateRight(a: array<int>)
  requires a.Length > 0
  modifies a
  ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)]) 
  ensures a[0] == old(a[a.Length-1])
{
  /* code modified by LLM (iteration 2): Fixed array type and maintained correct implementation */
  if a.Length == 1 { return; }
  
  var temp := a[a.Length-1];
  var i := a.Length - 1;
  
  while i > 0
    invariant 0 <= i <= a.Length - 1
    invariant temp == old(a[a.Length-1])
    invariant forall j :: i < j < a.Length ==> a[j] == old(a[j-1])
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[j])
  {
    a[i] := a[i-1];
    i := i - 1;
  }
  
  a[0] := temp;
}