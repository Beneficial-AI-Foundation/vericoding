// <vc-preamble>
// Method that copies elements from src to dst where mask is true, 
// preserving dst elements where mask is false
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method copyto<T>(dst: seq<T>, src: seq<T>, mask: seq<bool>) returns (result: seq<T>)
  // All input sequences must have the same length
  requires |dst| == |src| == |mask|
  // Result has the same length as inputs
  ensures |result| == |dst|
  // For each position i, result[i] is src[i] if mask[i] is true, otherwise dst[i]
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] == (if mask[i] then src[i] else dst[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): [Switched to an imperative loop to avoid a compiler error with sequence comprehensions.] */
  var i := 0;
  var temp_result: seq<T> := [];
  while i < |dst|
    invariant 0 <= i <= |dst|
    invariant |temp_result| == i
    invariant forall k :: 0 <= k < i ==> temp_result[k] == (if mask[k] then src[k] else dst[k])
  {
    if mask[i] {
      temp_result := temp_result + [src[i]];
    } else {
      temp_result := temp_result + [dst[i]];
    }
    i := i + 1;
  }
  result := temp_result;
}
// </vc-code>
