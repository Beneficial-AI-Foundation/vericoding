// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method update_elements(a: array<int>) returns (result: array<int>)
    requires a.Length >= 8
    ensures result.Length == a.Length
    ensures result[4] == a[4] + 3
    ensures result[7] == 516
    ensures forall i :: 0 <= i < a.Length && i != 4 && i != 7 ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  result := new int[a.Length];
  result[4] := a[4] + 3;
  result[7] := 516;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i && j != 4 && j != 7 ==> result[j] == a[j]
    invariant result[4] == a[4] + 3
    invariant result[7] == 516
    decreases a.Length - i
  {
    if i != 4 && i != 7 {
      result[i] := a[i];
    }
    i := i + 1;
  }
}
// </vc-code>
