// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method copy(arr: seq<int>) returns (result: seq<int>)
    ensures
        |result| == |arr| &&
        forall i :: 0 <= i < |arr| ==> result[i] == arr[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added invariant i <= |arr| to prove safety of arr[k] access and correctness of loop termination. */
  var i := 0;
  result := [];
  while i < |arr|
    invariant |result| == i
    invariant i <= |arr|
    invariant forall k :: 0 <= k < i ==> result[k] == arr[k]
  {
    result := result + [arr[i]];
    i := i + 1;
  }
}
// </vc-code>
