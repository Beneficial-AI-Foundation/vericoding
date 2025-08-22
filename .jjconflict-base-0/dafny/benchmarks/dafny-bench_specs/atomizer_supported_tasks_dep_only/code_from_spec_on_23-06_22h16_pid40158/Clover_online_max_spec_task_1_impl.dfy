// IMPL 
method onlineMax(a: array<int>, x: int) returns (ghost m:int, p:int)
  requires 1<=x<a.Length
  requires a.Length!=0
  ensures x<=p<a.Length
  ensures forall i::0<=i<x==> a[i]<=m
  ensures exists i::0<=i<x && a[i]==m
  ensures x<=p<a.Length-1 ==> (forall i::0<=i<p ==> a[i]<a[p])
  ensures (forall i::x<=i<a.Length && a[i]<=m) ==> p==a.Length-1
{
  /* code modified by LLM (iteration 4): Find maximum in a[0..x) with correct invariants */
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
  
  /* code modified by LLM (iteration 4): Check if all elements from x onwards are <= m */
  var allFromXLessOrEqualM := true;
  i := x;
  while i < a.Length
    invariant x <= i <= a.Length
    invariant allFromXLessOrEqualM ==> forall j :: x <= j < i ==> a[j] <= m
  {
    if a[i] > m {
      allFromXLessOrEqualM := false;
      break;
    }
    i := i + 1;
  }
  
  if allFromXLessOrEqualM {
    /* code modified by LLM (iteration 4): All elements from x onwards are <= m, so use last index */
    p := a.Length - 1;
  } else {
    /* code modified by LLM (iteration 4): Find valid p by checking postcondition requirements */
    p := x;
    while p < a.Length - 1
      invariant x <= p < a.Length
    {
      // Check if current p satisfies: forall i::0<=i<p ==> a[i]<a[p]
      var satisfiesCondition := true;
      var j := 0;
      while j < p
        invariant 0 <= j <= p
        invariant satisfiesCondition ==> forall k :: 0 <= k < j ==> a[k] < a[p]
      {
        if a[j] >= a[p] {
          satisfiesCondition := false;
          break;
        }
        j := j + 1;
      }
      
      if satisfiesCondition {
        return;
      }
      
      p := p + 1;
    }
    
    /* code modified by LLM (iteration 4): If we reach here, p == a.Length - 1 */
    // At this point p == a.Length - 1, which satisfies x <= p < a.Length
  }
}