//ATOM
/* code modified by LLM (iteration 1): Fixed incomplete method definitions and removed malformed code blocks */
method Cube(n: nat) returns (c: nat) 
  ensures c == n * n * n
{
  c := n * n * n;
}

//ATOM
function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}

//ATOM
/* code modified by LLM (iteration 1): Fixed method definition and implementation */
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
  var i := 0;
  while i < a.Length0
    invariant 0 <= i <= a.Length0
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj]) + 1
    invariant forall ii, jj :: i <= ii < a.Length0 && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj])
  {
    var j := 0;
    while j < a.Length1
      invariant 0 <= j <= a.Length1
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj]) + 1
      invariant forall jj :: 0 <= jj < j ==> a[i,jj] == old(a[i,jj]) + 1
      invariant forall jj :: j <= jj < a.Length1 ==> a[i,jj] == old(a[i,jj])
      invariant forall ii, jj :: i < ii < a.Length0 && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj])
    {
      a[i,j] := a[i,j] + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}