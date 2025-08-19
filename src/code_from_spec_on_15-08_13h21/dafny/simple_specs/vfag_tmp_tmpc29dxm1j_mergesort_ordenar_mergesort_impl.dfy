// The `ordenar_mergesort` method should be a wrapper that calls the `mergesort` method with appropriate parameters to sort the entire array.

//ATOM
method mergesort(V : array?<int>, c : int, f : int) 
  requires V != null
  requires c >= 0 && f <= V.Length
  modifies V
{
}

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
method ordenar_mergesort(V : array?<int>)
  requires V != null
  modifies V
{
  /* code modified by LLM (iteration 1): fixed compilation error by adding proper comment syntax */
  mergesort(V, 0, V.Length);
}