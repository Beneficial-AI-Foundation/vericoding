// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function getChoiceElement(choices: seq<seq<real>>, row: nat, col: nat): real
  requires row < |choices|
  requires col < |choices[row]|
{
  choices[row][col]
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
  result := seq(|indices|, i requires 0 <= i < |indices| => getChoiceElement(choices, indices[i], i));
}
// </vc-code>
