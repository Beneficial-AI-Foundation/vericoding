// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): require res to be at least length k to avoid index out-of-range when accessing res[i] */
lemma SquareInvariant(arr: array<int>, res: array<int>, k: int)
  requires 0 <= k <= arr.Length
  requires res.Length >= k
  requires forall i :: 0 <= i < k ==> res[i] == arr[i]*arr[i]
  ensures forall i :: 0 <= i < k ==> res[i] == arr[i]*arr[i]
{
  // Trivial: the postcondition follows from the third precondition
}

// </vc-helpers>

// <vc-spec>
method Square(arr: array<int>) returns (result: array<int>)
    ensures
        result.Length == arr.Length &&
        forall i :: 0 <= i < arr.Length ==> result[i] == arr[i] * arr[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented square computation with proper invariants */
  result := new int[arr.Length];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> result[j] == arr[j] * arr[j]
    decreases arr.Length - i
  {
    result[i] := arr[i] * arr[i];
    i := i + 1;
  }
}

// </vc-code>
