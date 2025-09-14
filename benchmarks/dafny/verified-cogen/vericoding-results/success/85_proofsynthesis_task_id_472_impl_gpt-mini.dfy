// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple min function */
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(arr: array<int>) returns (is_consecutive: bool)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> (0 <= arr[i] + 1 < 2147483647)
    ensures is_consecutive == (forall i, j :: 0 <= i < j < arr.Length && j == i + 1 ==> (arr[i] + 1 == arr[j]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate pairs and maintain invariant avoiding index OOB */
  var i := 0;
  is_consecutive := true;
  while i < arr.Length - 1
    invariant 0 <= i <= arr.Length - 1
    invariant is_consecutive == (forall k :: 0 <= k < i ==> arr[k] + 1 == arr[k+1])
  {
    if arr[i] + 1 != arr[i+1] {
      is_consecutive := false;
      assert exists k, j :: k == i && j == i + 1 && 0 <= k < j < arr.Length && arr[k] + 1 != arr[j];
      return;
    }
    i := i + 1;
  }
  return;
}
// </vc-code>
