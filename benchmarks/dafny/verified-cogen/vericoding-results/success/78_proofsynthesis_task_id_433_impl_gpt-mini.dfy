// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause and ensured i is within array bounds */
predicate PrefixGreater(arr: array<int>, number: int, i: int) reads arr { 0 <= i <= arr.Length && forall j :: 0 <= j < i ==> number > arr[j] }
// </vc-helpers>

// <vc-spec>
method IsGreater(arr: array<int>, number: int) returns (result: bool)
    ensures result == (forall i :: 0 <= i < arr.Length ==> number > arr[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): use PrefixGreater helper to check entire array */
  result := PrefixGreater(arr, number, arr.Length);
}
// </vc-code>
