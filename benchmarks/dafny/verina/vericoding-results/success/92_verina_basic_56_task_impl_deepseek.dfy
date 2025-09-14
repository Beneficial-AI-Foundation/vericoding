// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SeqSlice<T>(s: seq<T>, start: nat, len: nat): seq<T> requires start + len <= |s| { s[start..start+len] }
function SeqUpdate<T>(original: seq<T>, start: nat, segment: seq<T>): seq<T> requires start + |segment| <= |original| { original[0..start] + segment + original[start+|segment|..] }
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
  /* code modified by LLM (iteration 2): Fixed sequence slicing with bounds check */
  var copiedSegment := src[s_start..s_start + len];
  result := dest[0..d_start] + copiedSegment + dest[d_start + len..];
}
// </vc-code>
