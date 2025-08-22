// SPEC
method AllSequencesEqualLength(sequences: seq<seq<int>>) returns (result: bool)
  ensures result <==> forall i, j :: 0 <= i < |sequences| && 0 <= j < |sequences| ==> |sequences[i]| == |sequences[j]|
{
}
