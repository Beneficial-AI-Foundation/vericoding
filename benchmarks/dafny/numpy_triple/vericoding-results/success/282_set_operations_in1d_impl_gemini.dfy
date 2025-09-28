// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): No change needed, helper is correct. */
predicate Contains<T(==)>(s: seq<T>, val: T)
{
  exists i :: 0 <= i < |s| && s[i] == val
}
// </vc-helpers>

// <vc-spec>
method In1d<T(==)>(ar1: seq<T>, ar2: seq<T>) returns (result: seq<bool>)
  // The result has the same length as the first input array
  ensures |result| == |ar1|
  // Each element in the result indicates membership: result[i] is true iff ar1[i] exists in ar2
  ensures forall i :: 0 <= i < |ar1| ==> 
    (result[i] <==> exists j :: 0 <= j < |ar2| && ar1[i] == ar2[j])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Replaced sequence comprehension with a while loop to fix verification error. */
  result := [];
  var i := 0;
  while i < |ar1|
    invariant |result| == i
    invariant 0 <= i <= |ar1|
    invariant forall k :: 0 <= k < i ==> (result[k] <==> Contains(ar2, ar1[k]))
  {
    result := result + [Contains(ar2, ar1[i])];
    i := i + 1;
  }
}
// </vc-code>
