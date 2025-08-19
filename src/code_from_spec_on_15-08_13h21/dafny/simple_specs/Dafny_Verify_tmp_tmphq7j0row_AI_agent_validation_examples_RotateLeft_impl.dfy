method Cube_Example(n: nat) returns (c: nat) 
  ensures c == n * n * n
{
  c := n * n * n;
  return c;
}

//ATOM
method CopyMatrix_Example(src: array2<int>, dst: array2<int>)
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
  ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{
  var i := 0;
  while i < src.Length0
    invariant 0 <= i <= src.Length0
    /* code modified by LLM (iteration 1): Changed old(src[x,y]) to src[x,y] since src is not modified */
    invariant forall x, y :: 0 <= x < i && 0 <= y < src.Length1 ==> dst[x,y] == src[x,y]
  {
    var j := 0;
    while j < src.Length1
      invariant 0 <= j <= src.Length1
      /* code modified by LLM (iteration 1): Changed old(src[x,y]) to src[x,y] since src is not modified */
      invariant forall x, y :: 0 <= x < i && 0 <= y < src.Length1 ==> dst[x,y] == src[x,y]
      /* code modified by LLM (iteration 3): Corrected invariant to reference src instead of old(src) since src is not modified */
      invariant forall y :: 0 <= y < j ==> dst[i,y] == src[i,y]
    {
      dst[i,j] := src[i,j];
      j := j + 1;
    }
    i := i + 1;
  }
}

//ATOM
method IncrementMatrix_Example(a: array2<int>)
  modifies a
  ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
  var i := 0;
  while i < a.Length0
    invariant 0 <= i <= a.Length0
    invariant forall x, y :: 0 <= x < i && 0 <= y < a.Length1 ==> a[x,y] == old(a[x,y]) + 1
    invariant forall x, y :: i <= x < a.Length0 && 0 <= y < a.Length1 ==> a[x,y] == old(a[x,y])
  {
    var j := 0;
    while j < a.Length1
      invariant 0 <= j <= a.Length1
      invariant forall x, y :: 0 <= x < i && 0 <= y < a.Length1 ==> a[x,y] == old(a[x,y]) + 1
      invariant forall x, y :: i < x < a.Length0 && 0 <= y < a.Length1 ==> a[x,y] == old(a[x,y])
      invariant forall y :: 0 <= y < j ==> a[i,y] == old(a[i,y]) + 1
      invariant forall y :: j <= y < a.Length1 ==> a[i,y] == old(a[i,y])
    {
      a[i,j] := a[i,j] + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}

//ATOM
method Max_Example(a: array<nat>) returns (m: int)
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
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
method DoubleArray_Example(src: array<int>, dst: array<int>)
  requires src.Length == dst.Length
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{
  var i := 0;
  while i < src.Length
    invariant 0 <= i <= src.Length
    /* code modified by LLM (iteration 1): Changed 2 * src[j] to 2 * old(src[j]) to match postcondition and since old() is valid for unmodified src */
    invariant forall j :: 0 <= j < i ==> dst[j] == 2 * old(src[j])
  {
    dst[i] := 2 * src[i];
    i := i + 1;
  }
}

//IMPL 
method RotateLeft(a: array<int>)
  requires a.Length > 0
  modifies a
  ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]) 
  ensures a[a.Length -1] == old(a[0])
{
  if a.Length == 1 {
    return;
  }
  
  var temp := a[0];
  var i := 0;
  
  while i < a.Length - 1
    invariant 0 <= i <= a.Length - 1
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[j+1])
    invariant forall j :: i < j < a.Length ==> a[j] == old(a[j])
    invariant temp == old(a[0])
  {
    a[i] := a[i + 1];
    i := i + 1;
  }
  
  a[a.Length - 1] := temp;
}