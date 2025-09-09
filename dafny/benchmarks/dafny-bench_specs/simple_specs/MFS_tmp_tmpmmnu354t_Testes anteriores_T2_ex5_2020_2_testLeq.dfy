//ATOM
method leq(a: array<int>, b: array<int>) returns (result: bool) 
  ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
{
  result := false;
  assume result <==> (a.Length <= b.Length && a[..] ==> b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] ==> b[..k] && a[k] < b[k]);
  return result;
}


// SPEC

method testLeq() {
}
