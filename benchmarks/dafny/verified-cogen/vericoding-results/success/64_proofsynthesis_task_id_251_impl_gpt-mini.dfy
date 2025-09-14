// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple predicate for evenness */
function IsEven(n: int): bool { n % 2 == 0 }
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
  /* code modified by LLM (iteration 2): removed deprecated semicolons from invariants */
  result := new int[2 * arr.Length];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant result.Length == 2 * arr.Length
    invariant forall k :: 0 <= k < i ==> result[2 * k] == elem
    invariant forall k :: 0 <= k < i ==> result[2 * k + 1] == arr[k]
  {
    result[2 * i] := elem;
    result[2 * i + 1] := arr[i];
    i := i + 1;
  }
}
// </vc-code>
