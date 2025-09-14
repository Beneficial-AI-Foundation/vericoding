// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added reads and decreases clauses */
function IsSortedHelper(arr: array<int>, start: int): bool
  requires 0 <= start <= arr.Length
  reads arr
  decreases arr.Length - start
  ensures IsSortedHelper(arr, start) == (forall i, j :: start <= i < j < arr.Length ==> arr[i] <= arr[j])
{
  if start >= arr.Length - 1 then
    true
  else
    arr[start] <= arr[start+1] && IsSortedHelper(arr, start+1)
}
// </vc-helpers>

// <vc-spec>
method IsSorted(arr: array<int>) returns (is_sorted: bool)

    requires
        arr.Length > 0

    ensures
        is_sorted == (forall i, j :: 0 <= i < j < arr.Length ==> (arr[i] <= arr[j]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): unchanged, but helper was fixed */
  is_sorted := IsSortedHelper(arr, 0);
}
// </vc-code>
