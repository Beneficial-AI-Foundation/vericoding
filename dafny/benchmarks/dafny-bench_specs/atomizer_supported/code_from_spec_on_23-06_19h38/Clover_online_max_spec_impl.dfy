//IMPL 
method onlineMax(a: array<int>, x: int) returns (ghost m:int, p:int)
  requires 1<=x<a.Length
  requires a.Length!=0
  ensures x<=p<a.Length
  ensures forall i::0<=i<x==> a[i]<=m
  ensures exists i::0<=i<x && a[i]==m
  ensures x<=p<a.Length-1 ==> (forall i::0<=i<p ==> a[i]<a[p])
  ensures (forall i::x<=i<a.Length && a[i]<=m) ==> p==a.Length-1
{
  // Find the maximum in the prefix a[0..x)
  m := a[0];
  var i := 1;
  while i < x
    /* code modified by LLM (iteration 4): corrected loop invariants for maximum finding */
    invariant 1 <= i <= x
    invariant forall j :: 0 <= j < i ==> a[j] <= m
    invariant exists j :: 0 <= j < i && a[j] == m
  {
    if a[i] > m {
      m := a[i];
    }
    i := i + 1;
  }
  
  // Find the first position p >= x where a[p] > m, or set p to last index
  p := x;
  while p < a.Length - 1 && a[p] <= m
    /* code modified by LLM (iteration 4): simplified and corrected loop invariants */
    invariant x <= p < a.Length
    invariant forall j :: x <= j < p ==> a[j] <= m
    decreases a.Length - 1 - p
  {
    p := p + 1;
  }
  
  /* code modified by LLM (iteration 4): added explicit proof for fourth postcondition */
  // The fourth postcondition needs explicit proof
  if p < a.Length - 1 {
    // We exited the loop because a[p] > m (since p < a.Length - 1)
    assert a[p] > m;
    
    // Prove all elements before p are < a[p]
    forall j | 0 <= j < p
      ensures a[j] < a[p]
    {
      if j < x {
        // j is in prefix [0, x), so a[j] <= m < a[p]
        assert a[j] <= m < a[p];
      } else {
        // x <= j < p, so a[j] <= m by loop invariant
        assert a[j] <= m < a[p];
      }
    }
  }
}