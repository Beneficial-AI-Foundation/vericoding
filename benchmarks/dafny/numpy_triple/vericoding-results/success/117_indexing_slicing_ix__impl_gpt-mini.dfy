// <vc-preamble>
// Method to construct an open mesh from two 1-D integer sequences
// </vc-preamble>

// <vc-helpers>
lemma SeqWrapPreserve<T>(s: seq<T>)
  ensures ([s])[0] == s
{
}

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
  var r1: seq<seq<int>> := [];
  var i := 0;
  while i < |seq1|
    invariant 0 <= i <= |seq1|
    invariant |r1| == i
    invariant forall k :: 0 <= k < i ==> |r1[k]| == 1 && r1[k][0] == seq1[k]
  {
    r1 := r1 + [[seq1[i]]];
    i := i + 1;
  }
  var r2: seq<seq<int>> := [seq2];
  result1 := r1;
  result2 := r2;
}

// </vc-code>
