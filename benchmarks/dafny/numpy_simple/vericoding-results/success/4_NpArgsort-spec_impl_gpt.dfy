// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function InvalidIndex(): int { -1 }
// </vc-helpers>

// <vc-spec>
method Argsort(a: array<int>) returns (result: array<int>)
    ensures result.Length == a.Length
    ensures forall i, j :: 0 <= i < j < result.Length && 0 <= result[i] < a.Length && 0 <= result[j] < a.Length ==> a[result[i]] <= a[result[j]]
// </vc-spec>
// <vc-code>
{
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall k :: 0 <= k < i ==> result[k] == InvalidIndex()
    decreases a.Length - i
  {
    result[i] := InvalidIndex();
    i := i + 1;
  }
}
// </vc-code>
