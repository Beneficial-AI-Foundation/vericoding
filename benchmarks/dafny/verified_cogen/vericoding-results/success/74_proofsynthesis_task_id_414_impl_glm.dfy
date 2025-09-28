// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed Contains predicate to check for value presence */
predicate Contains(arr: array<int>, x: int) reads arr { exists j :: 0 <= j < arr.Length && arr[j] == x }
// </vc-helpers>

// <vc-spec>
method AnyValueExists(arr1: array<int>, arr2: array<int>) returns (result: bool)
    ensures result == exists k :: 0 <= k < arr1.Length && k in arr2[..]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed unresolved identifier by replacing k with i in the condition */
{
  var i := 0;
  while i < arr1.Length
      invariant 0 <= i <= arr1.Length
      invariant forall k :: 0 <= k < i ==> k !in arr2[..]
  {
      if i in arr2[..] {
          return true;
      }
      i := i + 1;
  }
  return false;
}
// </vc-code>
