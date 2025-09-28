// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added trigger to quantifier in ensures clause */
function DoCopy(src: seq<int>, s_start: nat, dest: seq<int>, d_start: nat, len: nat): seq<int>
    requires |src| >= s_start + len
    requires |dest| >= d_start + len
    ensures |DoCopy(src, s_start, dest, d_start, len)| == |dest|
    ensures forall i :: 0 <= i < d_start ==> DoCopy(src, s_start, dest, d_start, len)[i] == dest[i]
    ensures forall i :: d_start + len <= i < |DoCopy(src, s_start, dest, d_start, len)| ==> DoCopy(src, s_start, dest, d_start, len)[i] == dest[i]
    ensures forall i {:trigger DoCopy(src, s_start, dest, d_start, len)[d_start + i]} :: 0 <= i < len ==> DoCopy(src, s_start, dest, d_start, len)[d_start + i] == src[s_start + i]
{
    dest[0..d_start] + src[s_start..s_start+len] + dest[d_start+len..]
}
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
    result := DoCopy(src, s_start, dest, d_start, len);
}
// </vc-code>
