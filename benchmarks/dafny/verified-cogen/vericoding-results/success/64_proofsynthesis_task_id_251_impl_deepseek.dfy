// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }

lemma CopyArrayPreservesElements(source: array?<int>, target: array?<int>, start: int)
  requires source != null && target != null
  requires 0 <= start && start + source.Length <= target.Length
  requires forall i :: 0 <= i < source.Length ==> target[start + i] == source[i]
{
}

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
  /* code modified by LLM (iteration 2): Updated to fix type warnings */
  result := new int[2 * arr.Length];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < i ==> result[2 * k] == elem
    invariant forall k :: 0 <= k < i ==> result[2 * k + 1] == arr[k]
  {
    result[2 * i] := elem;
    result[2 * i + 1] := arr[i];
    i := i + 1;
  }
}
// </vc-code>
