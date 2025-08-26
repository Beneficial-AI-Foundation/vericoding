method append(a:array<int>, b:int) returns (c:array<int>)
  ensures  a[..] + [b] == c[..]
// </vc-spec>
// <vc-code>
{
  c := new int[a.Length + 1];
  
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant c[..i] == a[..i]
  {
    c[i] := a[i];
    i := i + 1;
  }
  
  c[a.Length] := b;
}
// </vc-code>