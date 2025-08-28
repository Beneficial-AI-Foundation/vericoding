// <vc-helpers>
// No additional helpers needed for this verification.
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ArraySplit (a : array<int>) returns (b : array<int>, c : array<int>)
  ensures fresh(b)
  ensures fresh(c)
  ensures a[..] == b[..] + c[..]
  ensures a.Length == b.Length + c.Length
  ensures a.Length > 1 ==> a.Length > b.Length
  ensures a.Length > 1 ==> a.Length > c.Length
// </vc-spec>
// </vc-spec>

// <vc-code>
method ArraySplitImpl (a : array<int>) returns (b : array<int>, c : array<int>)
  ensures fresh(b)
  ensures fresh(c)
  ensures a[..] == b[..] + c[..]
  ensures a.Length == b.Length + c.Length
  ensures a.Length > 1 ==> a.Length > b.Length
  ensures a.Length > 1 ==> a.Length > c.Length
{
  var splitPoint := if a.Length <= 1 then a.Length else a.Length / 2;
  b := new int[splitPoint];
  c := new int[a.Length - splitPoint];
  
  var i := 0;
  while i < splitPoint
    invariant 0 <= i <= splitPoint
    invariant forall k :: 0 <= k < i ==> b[k] == a[k]
  {
    b[i] := a[i];
    i := i + 1;
  }
  
  i := 0;
  while i < a.Length - splitPoint
    invariant 0 <= i <= a.Length - splitPoint
    invariant forall k :: 0 <= k < i ==> c[k] == a[splitPoint + k]
  {
    c[i] := a[splitPoint + i];
    i := i + 1;
  }
  
  // Strengthen the assertions by ensuring the loop invariants hold for the full range after the loops
  assert forall k :: 0 <= k < splitPoint ==> b[k] == a[k];
  assert forall k :: 0 <= k < a.Length - splitPoint ==> c[k] == a[splitPoint + k];
}
// </vc-code>
