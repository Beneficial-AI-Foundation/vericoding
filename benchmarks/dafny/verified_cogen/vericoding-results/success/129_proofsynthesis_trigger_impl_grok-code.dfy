// <vc-preamble>
function f(s: seq<int>, i: int): bool
    requires 0 <= i < |s|
{
    s[i] == i + 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added lemma to extract f property for specific index */
lemma ProveProperty(arr: array<int>, i: int)
  requires 0 <= i < arr.Length
  requires forall j :: 0 <= j < arr.Length ==> f(arr[..], j)
  ensures arr[i] == i + 2
{
  assert f(arr[..], i);
}
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
/* code modified by LLM (iteration 2): call helper lemma before assigning ret */
{
  ProveProperty(arr, i);
  ret := arr[i];
}
// </vc-code>
