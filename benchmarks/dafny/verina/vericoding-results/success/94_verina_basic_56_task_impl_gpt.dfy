// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Provide slice replacement utility for copying between sequences */
function ReplaceSlice(src: seq<int>, s_start: nat, dest: seq<int>, d_start: nat, len: nat): seq<int>
  requires |src| >= s_start + len
  requires |dest| >= d_start + len
{
  dest[0..d_start] + src[s_start .. s_start + len] + dest[d_start + len .. |dest|]
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
  /* code modified by LLM (iteration 3): Build result by concatenating prefix, middle (from src), and suffix */
  result := dest[0..d_start] + src[s_start .. s_start + len] + dest[d_start + len .. |dest|];
}
// </vc-code>
