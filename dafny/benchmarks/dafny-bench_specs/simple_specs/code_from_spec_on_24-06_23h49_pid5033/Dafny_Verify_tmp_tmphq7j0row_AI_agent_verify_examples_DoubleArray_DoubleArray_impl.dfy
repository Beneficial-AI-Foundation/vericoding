//IMPL 
method DoubleArray(src: array<int>, dst: array<int>)
  requires src.Length == dst.Length
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{
  var i := 0;
  while i < src.Length
    invariant 0 <= i <= src.Length
    /* code modified by LLM (iteration 4): updated invariant to match postcondition using old(src[j]) since src is unmodified */
    invariant forall j :: 0 <= j < i ==> dst[j] == 2 * old(src[j])
  {
    dst[i] := 2 * src[i];
    i := i + 1;
  }
}