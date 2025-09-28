// <vc-preamble>
function MultisetCount<T(==)>(s: seq<T>, x: T): nat
{
    |set i | 0 <= i < |s| && s[i] == x|
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Sort(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        (forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]) &&
        (forall x :: MultisetCount(result[..], x) == MultisetCount(a[..], x))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed quantification of variable l in invariant */
  var b := new int[a.Length];
  for i := 0 to a.Length - 1
  {
    b[i] := a[i];
  }
  for i := 0 to b.Length - 1
    invariant forall x :: MultisetCount(b[..], x) == MultisetCount(a[..], x)
    invariant forall k, l :: 0 <= k < l < i ==> b[k] <= b[l]
    invariant forall k, l :: 0 <= k < i && i <= l < b.Length ==> b[k] <= b[l]
  {
    var minIndex := i;
    for j := i+1 to b.Length - 1
      invariant i <= minIndex < b.Length
      invariant forall k :: i <= k < j ==> b[minIndex] <= b[k]
    {
      if b[j] < b[minIndex] {
        minIndex := j;
      }
    }
    var temp := b[i];
    b[i] := b[minIndex];
    b[minIndex] := temp;
  }
  return b;
}
// </vc-code>
