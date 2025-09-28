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
  /* code modified by LLM (iteration 5): strengthened loop invariant to ensure result elements match postcondition */
  result := [];
  var i: nat := 0;
  while i < |indices|
    invariant 0 <= i <= |indices|
    invariant |result| == i
    invariant forall j :: 0 <= j < |result| ==> result[j] == choices[indices[j]][j]
  {
    result := result + [choices[indices[i]][i]];
    i := i + 1;
  }
}
// </vc-code>
