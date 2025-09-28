// <vc-preamble>
function f(s: seq<int>, i: int): bool
    requires 0 <= i < |s|
{
    s[i] == i + 2
}
// </vc-preamble>

// <vc-helpers>
lemma ArraySeqIndexEquality(a: array<int>, i: int)
  requires 0 <= i < a.Length
  ensures a[i] == a[..][i]
{ }
// </vc-helpers>

// <vc-spec>
method GetElementCheckProperty(arr: array<int>, i: int) returns (ret: int)
    requires arr.Length > 0
    requires 0 < i < arr.Length
    requires forall j :: 0 <= j < arr.Length ==> f(arr[..], j)
    ensures ret == i + 2
    ensures ret == arr[i]
// </vc-spec>
// <vc-code>
{
  assert 0 <= i < arr.Length;
  assert f(arr[..], i);
  assert arr[..][i] == i + 2;
  ArraySeqIndexEquality(arr, i);
  ret := arr[i];
}
// </vc-code>
