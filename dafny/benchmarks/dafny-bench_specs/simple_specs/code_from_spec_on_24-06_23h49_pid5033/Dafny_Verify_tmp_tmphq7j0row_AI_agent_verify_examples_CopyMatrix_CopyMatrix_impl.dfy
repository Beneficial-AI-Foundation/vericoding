//IMPL 
method CopyMatrix(src: array2<int>, dst: array2<int>)
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
  ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{
  var i := 0;
  while i < src.Length0
    invariant 0 <= i <= src.Length0
    /* code modified by LLM (iteration 3): Enhanced invariant to capture all copied elements up to row i */
    invariant forall r, c :: 0 <= r < i && 0 <= c < src.Length1 ==> dst[r,c] == src[r,c]
  {
    var j := 0;
    while j < src.Length1
      invariant 0 <= j <= src.Length1
      invariant 0 <= i < src.Length0
      /* code modified by LLM (iteration 3): Invariant for previously completed rows */
      invariant forall r, c :: 0 <= r < i && 0 <= c < src.Length1 ==> dst[r,c] == src[r,c]
      /* code modified by LLM (iteration 3): Invariant for current row progress */
      invariant forall c :: 0 <= c < j ==> dst[i,c] == src[i,c]
    {
      dst[i,j] := src[i,j];
      j := j + 1;
    }
    i := i + 1;
  }
}