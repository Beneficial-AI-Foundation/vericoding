// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma IndicesWithinBounds(n: int, i: int)
  requires 0 <= i < n
  ensures 0 <= 2 * i < 2 * n
  ensures 0 <= 2 * i + 1 < 2 * n
{ }
// </vc-helpers>

// <vc-spec>
method InsertBeforeEach(arr: array<int>, elem: int) returns (result: array<int>)
    ensures
        result.Length == (2 * arr.Length) &&
        (forall k :: 0 <= k < arr.Length ==> result[2 * k] == elem) &&
        (forall k :: 0 <= k < arr.Length ==> result[2 * k + 1] == arr[k])
// </vc-spec>
// <vc-code>
{
  var n := arr.Length;
  result := new int[2 * n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == 2 * n
    invariant forall k :: 0 <= k < i ==> result[2 * k] == elem
    invariant forall k :: 0 <= k < i ==> result[2 * k + 1] == arr[k]
  {
    result[2 * i] := elem;
    result[2 * i + 1] := arr[i];
    i := i + 1;
  }
}
// </vc-code>
