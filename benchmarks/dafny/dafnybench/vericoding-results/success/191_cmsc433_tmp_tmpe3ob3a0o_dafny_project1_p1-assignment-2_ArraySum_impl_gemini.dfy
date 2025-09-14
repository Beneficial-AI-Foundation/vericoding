// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ArraySum (a : array<int>, b : array<int>) returns (c : array<int>)
    requires a.Length == b.Length
    ensures c.Length == a.Length && 
        forall i : int :: 0 <= i < c.Length ==> c[i] == a[i] + b[i]
// </vc-spec>
// <vc-code>
{
  c := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant c.Length == a.Length
    invariant forall j :: 0 <= j < i ==> c[j] == a[j] + b[j]
  {
    c[i] := a[i] + b[i];
    i := i + 1;
  }
}
// </vc-code>
