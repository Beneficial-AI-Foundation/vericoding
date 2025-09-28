// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function AllIndicesInRange(a: array<int>, b: array<int>): bool
  requires a.Length == b.Length
  reads a, b
{
  if a.Length == 0 then true
  else (forall i :: 0 <= i < a.Length ==> a[i] != b[i]) == (forall i :: 0 <= i < a.Length ==> a[i] != b[i])
}
// </vc-helpers>

// <vc-spec>
method NotEqual(a: array<int>, b: array<int>) returns (result: array<bool>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == (a[i] != b[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed compilation errors by adding reads clauses */
  var length := a.Length;
  result := new bool[length];
  var index := 0;
  
  while index < length
    invariant 0 <= index <= length
    invariant result.Length == length
    invariant forall j :: 0 <= j < index ==> result[j] == (a[j] != b[j])
  {
    result[index] := a[index] != b[index];
    index := index + 1;
  }
}
// </vc-code>
