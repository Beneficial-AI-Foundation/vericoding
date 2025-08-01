//IMPL
method leq(a: array<int>, b: array<int>) returns (result: bool) 
  ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
{
  var i := 0;
  while i < a.Length && i < b.Length && a[i] == b[i]
    invariant 0 <= i <= a.Length && i <= b.Length
    invariant a[..i] == b[..i]
  {
    i := i + 1;
  }
  
  if i == a.Length {
    result := true;
  } else if i == b.Length {
    result := false;
  } else {
    result := a[i] < b[i];
  }
}