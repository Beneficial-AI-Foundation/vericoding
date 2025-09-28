// <vc-preamble>
// Method that copies elements from src to dst where mask is true, 
// preserving dst elements where mask is false
// </vc-preamble>

// <vc-helpers>
function Select<T>(dst: T, src: T, m: bool): T { if m then src else dst }
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
  var n := |dst|;
  var res := dst;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == n
    invariant forall j :: 0 <= j < i ==> res[j] == (if mask[j] then src[j] else dst[j])
    invariant forall j :: i <= j < n ==> res[j] == dst[j]
  {
    if mask[i] {
      res := res[..i] + [src[i]] + res[i+1..];
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>
