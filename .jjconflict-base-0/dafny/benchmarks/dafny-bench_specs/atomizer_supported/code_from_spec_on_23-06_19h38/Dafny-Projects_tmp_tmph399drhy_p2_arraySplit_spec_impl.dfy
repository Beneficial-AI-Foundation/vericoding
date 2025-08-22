//IMPL 
method ArraySplit (a : array<int>) returns (b : array<int>, c : array<int>)
  ensures fresh(b)
  ensures fresh(c)
  ensures a[..] == b[..] + c[..]
  ensures a.Length == b.Length + c.Length
  ensures a.Length > 1 ==> a.Length > b.Length
  ensures a.Length > 1 ==> a.Length > c.Length
{
  if a.Length == 0 {
    b := new int[0];
    c := new int[0];
  } else if a.Length == 1 {
    b := new int[1];
    b[0] := a[0];
    c := new int[0];
  } else {
    var split := a.Length / 2;
    /* code modified by LLM (iteration 4): Added explicit bounds check for split value */
    assert a.Length >= 2;
    assert split >= 1 && split <= a.Length - 1;
    
    b := new int[split];
    c := new int[a.Length - split];
    
    var i := 0;
    while i < split
      invariant 0 <= i <= split
      invariant forall j :: 0 <= j < i ==> b[j] == a[j]
    {
      b[i] := a[i];
      i := i + 1;
    }
    
    i := 0;
    while i < a.Length - split
      invariant 0 <= i <= a.Length - split
      invariant forall j :: 0 <= j < i ==> c[j] == a[split + j]
    {
      c[i] := a[split + i];
      i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): Added comprehensive sequence equality proof */
    assert forall j :: 0 <= j < split ==> b[j] == a[j];
    assert forall j :: 0 <= j < a.Length - split ==> c[j] == a[split + j];
    assert b[..] == a[..split];
    assert c[..] == a[split..];
    
    // Prove the main sequence equality
    assert a[..] == a[..split] + a[split..];
    assert a[..] == b[..] + c[..];
    
    // Prove the size constraints
    assert b.Length == split < a.Length;
    assert c.Length == a.Length - split < a.Length;
  }
}