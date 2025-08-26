method SquareElements(a: array<int>) returns (squared: array<int>)
    ensures squared.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> squared[i] == a[i] * a[i]
// </vc-spec>
// <vc-code>
{
  squared := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> squared[j] == a[j] * a[j]
  {
    squared[i] := a[i] * a[i];
    i := i + 1;
  }
}
// </vc-code>