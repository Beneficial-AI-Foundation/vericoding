//ATOM
datatype Color = Red | White | Blue

//ATOM
predicate Below(c: Color, d: Color)
{
  c == Red || c == d || d == Blue
}

//IMPL 
method DutchFlag(a: array<Color>)
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> Below(a[i], a[j])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  if a.Length <= 1 {
    return;
  }
  
  var low := 0;
  var mid := 0;
  var high := a.Length - 1;
  
  /* code modified by LLM (iteration 1): added decreases clause to fix termination verification */
  while mid <= high
    invariant 0 <= low <= mid <= high + 1 <= a.Length
    invariant forall k :: 0 <= k < low ==> a[k] == Red
    invariant forall k :: low <= k < mid ==> a[k] == White
    invariant forall k :: high < k < a.Length ==> a[k] == Blue
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases high - mid
  {
    if a[mid] == Red {
      a[low], a[mid] := a[mid], a[low];
      low := low + 1;
      mid := mid + 1;
    } else if a[mid] == White {
      mid := mid + 1;
    } else { // a[mid] == Blue
      a[mid], a[high] := a[high], a[mid];
      high := high - 1;
    }
  }
}