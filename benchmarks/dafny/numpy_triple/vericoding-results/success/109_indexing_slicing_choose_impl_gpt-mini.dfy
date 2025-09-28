// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma ChoiceLengthsEqual(choices: seq<seq<real>>, len: int)
    requires forall c :: c in choices ==> |c| == len
    ensures forall idx :: 0 <= idx < |choices| ==> |choices[idx]| == len
{
  var i := 0;
  while i < |choices|
    invariant 0 <= i <= |choices|
    invariant forall k :: 0 <= k < i ==> |choices[k]| == len
  {
    assert choices[i] in choices;
    assert |choices[i]| == len;
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method Choose(indices: seq<nat>, choices: seq<seq<real>>) returns (result: seq<real>)
    requires |indices| > 0
    requires |choices| > 0
    requires forall i :: 0 <= i < |indices| ==> indices[i] < |choices|
    requires forall c :: c in choices ==> |c| == |indices|
    ensures |result| == |indices|
    ensures forall i :: 0 <= i < |result| ==> 
        result[i] == choices[indices[i]][i]
// </vc-spec>
// <vc-code>
{
  var a := new real[|indices|];
  ChoiceLengthsEqual(choices, |indices|);
  var i := 0;
  while i < |indices|
    invariant 0 <= i <= |indices|
    invariant forall j :: 0 <= j < i ==> a[j] == choices[indices[j]][j]
  {
    a[i] := choices[indices[i]][i];
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
