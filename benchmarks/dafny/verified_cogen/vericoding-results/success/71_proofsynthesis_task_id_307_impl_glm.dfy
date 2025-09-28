// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ListDeepClone(arr: array<int>) returns (copied: array<int>)
    ensures arr.Length == copied.Length
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == copied[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed loop bounds to handle empty arrays */
{
  copied := new int[arr.Length];
  for i := 0 to arr.Length
      invariant 0 <= i <= arr.Length
      invariant forall j :: 0 <= j < i ==> arr[j] == copied[j]
  {
      copied[i] := arr[i];
  }
}
// </vc-code>
