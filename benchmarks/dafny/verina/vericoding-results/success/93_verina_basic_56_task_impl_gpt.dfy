// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): retain simple min function for completeness */
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method Copy(src: seq<int>, s_start: nat, dest: seq<int>, d_start: nat, len: nat) returns (result: seq<int>)
    requires 
        |src| >= s_start + len
    requires
        |dest| >= d_start + len
    ensures
        |result| == |dest|
    ensures
        forall i :: 0 <= i < d_start ==> result[i] == dest[i]
    ensures
        forall i :: d_start + len <= i < |result| ==> result[i] == dest[i]
    ensures
        forall i {:trigger result[d_start + i]} :: 0 <= i < len ==> result[d_start + i] == src[s_start + i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build result using slices and concatenation to copy the specified segment */
  var prefix := dest[..d_start];
  var mid := src[s_start .. s_start + len];
  var suffix := dest[d_start + len ..];
  assert |prefix| == d_start;
  assert |mid| == len;
  result := prefix + mid + suffix;
}
// </vc-code>
