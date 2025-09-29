// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  result := [];
  var i := 0;
  while i < |indices|
    invariant 0 <= i <= |indices|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == choices[indices[j]][j]
  {
    result := result + [choices[indices[i]][i]];
    i := i + 1;
  }
}
// </vc-code>
