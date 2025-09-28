// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma ChoiceLengthFromMembership(choices: seq<seq<real>>, indices: seq<nat>, k: nat)
  requires forall c :: c in choices ==> |c| == |indices|
  requires k < |choices|
  ensures |choices[k]| == |indices|
{
  assert choices[k] in choices;
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
  var r: seq<real> := [];
  var i: int := 0;
  while i < |indices|
    invariant 0 <= i <= |indices|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == choices[indices[j]][j]
  {
    assert indices[i] < |choices|;
    assert choices[indices[i]] in choices;
    assert |choices[indices[i]]| == |indices|;
    r := r + [choices[indices[i]][i]];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
