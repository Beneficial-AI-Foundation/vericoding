method leq(a: array<int>, b: array<int>) returns (result: bool) 
    ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length && i < b.Length && a[i] == b[i]
    invariant 0 <= i <= a.Length
    invariant 0 <= i <= b.Length
    invariant a[..i] == b[..i]
  {
    i := i + 1;
  }
  
  if i < a.Length && i < b.Length {
    // We found a difference at position i
    result := a[i] < b[i];
  } else {
    // One array is a prefix of the other
    result := a.Length <= b.Length;
  }
}
// </vc-code>