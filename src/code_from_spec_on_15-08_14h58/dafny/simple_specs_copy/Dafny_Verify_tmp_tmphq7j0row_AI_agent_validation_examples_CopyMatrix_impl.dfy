/* code modified by LLM (iteration 1): Fixed orphaned code by removing invalid statements and properly structuring the Cube method */
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
/* code modified by LLM (iteration 1): Fixed orphaned code by removing invalid statements and properly structuring the IncrementMatrix method */
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

//ATOM
/* code modified by LLM (iteration 1): Fixed orphaned code by removing invalid statements and properly structuring the Max method */
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
      invariant forall j :: 0 <= j < i ==> a[j] <= m
      invariant exists j :: 0 <= j < i && m == a[j]
    {
      if a[i] > m {
        m := a[i];
      }
      i := i + 1;
    }
  }
}

//IMPL CopyMatrix
method CopyMatrix(src: array2, dst: array2)
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
  ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{
  var i := 0;
  while i < src.Length0
    invariant 0 <= i <= src.Length0
    /* code modified by LLM (iteration 4): Fixed invariant to properly establish postcondition using old(src) */
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < src.Length1 ==> dst[ii,jj] == old(src[ii,jj])
  {
    var j := 0;
    while j < src.Length1
      invariant 0 <= j <= src.Length1
      /* code modified by LLM (iteration 4): Fixed inner loop invariants to maintain old(src) relationship and use src directly since it's unmodified */
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < src.Length1 ==> dst[ii,jj] == old(src[ii,jj])
      invariant forall jj :: 0 <= jj < j ==> dst[i,jj] == src[i,jj]
    {
      dst[i,j] := src[i,j];
      j := j + 1;
    }
    i := i + 1;
  }
}