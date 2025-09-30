// <vc-preamble>
// Method to construct an open mesh from two 1-D integer sequences
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ix_(seq1: seq<int>, seq2: seq<int>) returns (result1: seq<seq<int>>, result2: seq<seq<int>>)
  ensures |result1| == |seq1|
  ensures |result2| == 1
  ensures forall i :: 0 <= i < |result1| ==> |result1[i]| == 1
  ensures forall i :: 0 <= i < |result2| ==> |result2[i]| == |seq2|
  ensures forall i :: 0 <= i < |seq1| ==> result1[i][0] == seq1[i]
  ensures forall j :: 0 <= j < |seq2| ==> result2[0][j] == seq2[j]
  ensures forall i, j :: 0 <= i < |seq1| && 0 <= j < |seq2| ==> 
    result1[i][0] == seq1[i] && result2[0][j] == seq2[j]
// </vc-spec>
// <vc-code>
{
  result1 := seq(|seq1|, i requires 0 <= i < |seq1| => [seq1[i]]);
  result2 := [seq2];
}
// </vc-code>
