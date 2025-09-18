// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 5): using proper sequence slicing to copy elements */
  result := dest[..d_start] + src[s_start..s_start + len] + dest[d_start + len..];
}
// </vc-code>
