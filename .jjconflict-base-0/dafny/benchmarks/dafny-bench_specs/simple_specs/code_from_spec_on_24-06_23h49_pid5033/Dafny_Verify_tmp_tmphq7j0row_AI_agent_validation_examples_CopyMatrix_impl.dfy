//IMPL CopyMatrix
method CopyMatrix(src: array2<int>, dst: array2<int>)
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
  ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == src[i,j] 
{
  var i := 0;
  while i < src.Length0
    invariant 0 <= i <= src.Length0
    /* code modified by LLM (iteration 1): Removed old() from src array access since src is not modified */
    invariant forall row, col :: 0 <= row < i && 0 <= col < src.Length1 ==> dst[row,col] == src[row,col]
  {
    var j := 0;
    while j < src.Length1
      invariant 0 <= j <= src.Length1
      /* code modified by LLM (iteration 1): Removed old() from src array access since src is not modified */
      invariant forall row, col :: 0 <= row < i && 0 <= col < src.Length1 ==> dst[row,col] == src[row,col]
      /* code modified by LLM (iteration 1): Removed old() from src array access since src is not modified */
      invariant forall col :: 0 <= col < j ==> dst[i,col] == src[i,col]
    {
      dst[i,j] := src[i,j];
      j := j + 1;
    }
    i := i + 1;
  }
}