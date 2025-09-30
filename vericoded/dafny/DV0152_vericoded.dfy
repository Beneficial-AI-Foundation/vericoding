// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Append(a: array<int>, b: int) returns (result: array<int>)
    ensures result.Length == a.Length + 1
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i]
    ensures result[a.Length] == b
// </vc-spec>
// <vc-code>
{
  result := new int[a.Length + 1];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == a[j]
  {
    result[i] := a[i];
    i := i + 1;
  }
  result[a.Length] := b;
}
// </vc-code>
