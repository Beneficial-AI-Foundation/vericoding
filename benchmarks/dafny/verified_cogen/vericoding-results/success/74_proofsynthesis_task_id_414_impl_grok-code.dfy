// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AnyValueExists(arr1: array<int>, arr2: array<int>) returns (result: bool)
    ensures result == exists k :: 0 <= k < arr1.Length && k in arr2[..]
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 2): Implement loop to check if any index k from 0 to len-1 is in arr2 sequence with appropriate invariants */
var i := 0;
while i < arr1.Length
  invariant 0 <= i <= arr1.Length
  invariant forall k :: 0 <= k < i ==> !(k in arr2[..])
{
  if i in arr2[..] {
    return true;
  }
  i := i + 1;
}
return false;
}
// </vc-code>
