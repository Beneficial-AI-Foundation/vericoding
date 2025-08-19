//ATOM
method mezclar(V: array?<int>, c : int, m : int, f : int)
  requires V != null
  requires c <= m <= f
  requires 0 <= c <= V.Length
  requires 0 <= m <= V.Length
  requires 0 <= f <= V.Length
  modifies V
{
}

//IMPL 
method mergesort(V : array?<int>, c : int, f : int) 
  requires V != null
  requires c >= 0 && f <= V.Length
  modifies V
  /* code modified by LLM (iteration 1): added decreases clause to prove termination */
  decreases f - c
{
  if c < f - 1 {
    var m := (c + f) / 2;
    mergesort(V, c, m);
    mergesort(V, m, f);
    mezclar(V, c, m, f);
  }
}