// <vc-preamble>
// Method that copies elements from src to dst where mask is true, 
// preserving dst elements where mask is false
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed generic type parameter syntax */
predicate validIndex<T>(i: int, s: seq<T>) {
  0 <= i < |s|
}

function copyElement<T>(dst: T, src: T, maskValue: bool): T {
  if maskValue then src else dst
}
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
  /* code modified by LLM (iteration 2): fixed implementation using sequence comprehension */
  result := seq(|dst|, i requires 0 <= i < |dst| => if mask[i] then src[i] else dst[i]);
}
// </vc-code>
