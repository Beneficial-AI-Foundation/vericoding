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

//IMPL mergesort
method mergesort(V : array?<int>, c : int, f : int) 
  requires V != null
  requires c >= 0 && f <= V.Length
  modifies V
{
  /* code modified by LLM (iteration 3): fixed bounds checking and removed invalid assertions */
  if c < f - 1 {
    var m := (c + f) / 2;
    
    /* code modified by LLM (iteration 3): verify bounds for recursive calls */
    assert c >= 0; // from method precondition
    assert f <= V.Length; // from method precondition
    assert c < f - 1; // from if condition, so c + 1 < f
    assert m >= c; // since m = (c + f) / 2 and c < f
    assert m < f; // since m = (c + f) / 2 and c < f
    assert m <= V.Length; // since m < f and f <= V.Length
    
    mergesort(V, c, m);
    mergesort(V, m, f);
    
    /* code modified by LLM (iteration 3): verify preconditions for mezclar call */
    assert c <= m; // m >= c from division properties
    assert m <= f; // m < f from division properties  
    assert 0 <= c; // from method precondition
    assert c <= V.Length; // since c < f - 1 < f and f <= V.Length
    assert 0 <= m; // since m >= c and c >= 0
    assert 0 <= f; // since f > c + 1 and c >= 0
    assert f <= V.Length; // from method precondition
    
    mezclar(V, c, m, f);
  }
}