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
  // Find the maximum in a[0..x)
  m := a[0];
  var i := 1;
  while i < x
    invariant 1 <= i <= x
    invariant forall j :: 0 <= j < i ==> a[j] <= m
    invariant exists j :: 0 <= j < i && a[j] == m
  {
    if a[i] > m {
      m := a[i];
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 4): Find the first position p >= x where a[p] > m, or return last index if none exists */
  p := x;
  while p < a.Length - 1 && a[p] <= m
    invariant x <= p <= a.Length - 1
    invariant forall j :: x <= j < p ==> a[j] <= m
  {
    p := p + 1;
  }
  
  /* code modified by LLM (iteration 4): Now p is either the first index >= x where a[p] > m, or a.Length-1 */
  
  /* code modified by LLM (iteration 4): Verify postcondition 4 */
  if x <= p < a.Length - 1 {
    /* code modified by LLM (iteration 4): We exited the loop because a[p] > m, so verify all before p are < a[p] */
    assert a[p] > m;
    forall j | 0 <= j < p
      ensures a[j] < a[p]
    {
      if j < x {
        assert a[j] <= m;
        assert m < a[p];
      } else {
        assert x <= j < p;
        assert a[j] <= m;
        assert m < a[p];
      }
    }
  }
  
  /* code modified by LLM (iteration 4): Verify postcondition 5 */
  if forall j :: x <= j < a.Length && a[j] <= m {
    /* code modified by LLM (iteration 4): If all suffix elements <= m, then we never found a[p] > m */
    assert p == a.Length - 1;
    assert a[p] <= m;
  }
}