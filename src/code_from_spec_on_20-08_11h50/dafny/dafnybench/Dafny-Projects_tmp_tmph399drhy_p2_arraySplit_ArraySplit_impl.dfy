// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ArraySplit (a : array<int>) returns (b : array<int>, c : array<int>)
  ensures fresh(b)
  ensures fresh(c)
  ensures a[..] == b[..] + c[..]
  ensures a.Length == b.Length + c.Length
  ensures a.Length > 1 ==> a.Length > b.Length
  ensures a.Length > 1 ==> a.Length > c.Length
// </vc-spec>
// <vc-code>
{
  if a.Length == 0 {
    b := new int[0];
    c := new int[0];
  } else if a.Length == 1 {
    b := new int[1];
    b[0] := a[0];
    c := new int[0];
  } else {
    // a.Length > 1, so we need to split such that both parts are non-empty
    // and both are strictly smaller than the original
    var mid := a.Length / 2;  // This ensures 1 <= mid < a.Length;
    
    b := new int[mid];
    c := new int[a.Length - mid];
    
    var i := 0;
    while i < mid
      invariant 0 <= i <= mid
      invariant forall j :: 0 <= j < i ==> b[j] == a[j]
    {
      b[i] := a[i];
      i := i + 1;
    }
    
    i := 0;
    while i < a.Length - mid
      invariant 0 <= i <= a.Length - mid
      invariant forall j :: 0 <= j < i ==> c[j] == a[mid + j]
      invariant forall j :: 0 <= j < mid ==> b[j] == a[j]
    {
      c[i] := a[mid + i];
      i := i + 1;
    }
    
    // Help Dafny prove the postcondition
    assert b[..] == a[..mid];
    assert c[..] == a[mid..];
    assert a[..] == a[..mid] + a[mid..];
  }
}
// </vc-code>