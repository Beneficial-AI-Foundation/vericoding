// <vc-preamble>
// Method that copies elements from src to dst where mask is true, 
// preserving dst elements where mask is false
// </vc-preamble>

// <vc-helpers>
function applyMask<T>(dst: seq<T>, src: seq<T>, mask: seq<bool>, i: int): T
  requires 0 <= i < |dst| && |dst| == |src| && |src| == |mask|
{
  if mask[i] then src[i] else dst[i]
}

lemma BuildResultLemma<T>(dst: seq<T>, src: seq<T>, mask: seq<bool>, n: int)
  requires |dst| == |src| == |mask|
  requires 0 <= n <= |dst|
  ensures forall i :: 0 <= i < n ==> 
    applyMask(dst, src, mask, i) == (if mask[i] then src[i] else dst[i])
{
  if n > 0 {
    BuildResultLemma(dst, src, mask, n-1);
  }
}

function buildResult<T>(dst: seq<T>, src: seq<T>, mask: seq<bool>, n: int): (r: seq<T>)
  requires |dst| == |src| == |mask|
  requires 0 <= n <= |dst|
  ensures |r| == n
  ensures forall i :: 0 <= i < n ==> r[i] == applyMask(dst, src, mask, i)
{
  if n == 0 then [] else buildResult(dst, src, mask, n-1) + [applyMask(dst, src, mask, n-1)]
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
  /* code modified by LLM (iteration 5): Fixed helper function return value and lemma application */
  var n := |dst|;
  result := buildResult(dst, src, mask, n);
  BuildResultLemma(dst, src, mask, n);
}
// </vc-code>
