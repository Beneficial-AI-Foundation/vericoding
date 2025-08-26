method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat) returns (r: array<int>)
  requires src.Length >= sStart + len
  requires dest.Length >= dStart + len
  ensures r.Length == dest.Length
  ensures r[..dStart] == dest[..dStart]
  ensures r[dStart + len..] == dest[dStart + len..]
  ensures r[dStart..len+dStart] == src[sStart..len+sStart]
// </vc-spec>
// <vc-code>
{
  r := new int[dest.Length];
  
  // Copy elements before the destination range
  var i := 0;
  while i < dStart
    invariant 0 <= i <= dStart
    invariant r[..i] == dest[..i]
  {
    r[i] := dest[i];
    i := i + 1;
  }
  
  // Copy elements from source to destination range
  i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant r[..dStart] == dest[..dStart]
    invariant r[dStart..dStart+i] == src[sStart..sStart+i]
  {
    r[dStart + i] := src[sStart + i];
    i := i + 1;
  }
  
  // Copy elements after the destination range
  i := dStart + len;
  while i < dest.Length
    invariant dStart + len <= i <= dest.Length
    invariant r[..dStart] == dest[..dStart]
    invariant r[dStart..dStart+len] == src[sStart..sStart+len]
    invariant r[dStart + len..i] == dest[dStart + len..i]
  {
    r[i] := dest[i];
    i := i + 1;
  }
  
  // At this point, we have i == dest.Length, so r[dStart + len..i] == dest[dStart + len..i]
  // becomes r[dStart + len..dest.Length] == dest[dStart + len..dest.Length]
  // which is equivalent to r[dStart + len..] == dest[dStart + len..]
  assert r[dStart + len..] == dest[dStart + len..];
}
// </vc-code>