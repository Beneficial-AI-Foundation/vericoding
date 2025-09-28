// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma LemmaModuloEqual(a: int, b: int)
  requires a % 2 == b % 2
  ensures a % 2 == b % 2
{
}

lemma LemmaModuloNotEqual(a: int, b: int)
  requires a % 2 != b % 2
  ensures a % 2 != b % 2
{
}

predicate IndexAndValueModuloMatch(i: int, value: int) {
  i % 2 == value % 2
}
// </vc-helpers>

// <vc-spec>
method IsOddAtOddIndex(arr: array<int>) returns (result: bool)
    ensures result == forall i :: 0 <= i < arr.Length ==> ((i % 2) == (arr[i] % 2))
// </vc-spec>
// <vc-code>
{
  result := true;
  var idx := 0;
  while idx < arr.Length
    invariant 0 <= idx <= arr.Length
    invariant result == (forall j :: 0 <= j < idx ==> IndexAndValueModuloMatch(j, arr[j]))
  {
    if arr[idx] % 2 != idx % 2 {
      result := false;
      break;
    }
    idx := idx + 1;
  }
}
// </vc-code>
