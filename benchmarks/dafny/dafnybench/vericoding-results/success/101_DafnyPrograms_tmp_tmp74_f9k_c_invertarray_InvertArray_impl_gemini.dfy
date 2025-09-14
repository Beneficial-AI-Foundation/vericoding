// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method InvertArray(a: array<int>)
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length-1-i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant forall j | 0 <= j < i :: a[j] == old(a[a.Length - 1 - j])
    invariant forall j | 0 <= j < i :: a[a.Length - 1 - j] == old(a[j])
    invariant forall j | i <= j < a.Length - i :: a[j] == old(a[j])
    modifies a
  {
    var tmp := a[i];
    a[i] := a[a.Length - 1 - i];
    a[a.Length - 1 - i] := tmp;
    i := i + 1;
  }
}
// </vc-code>
