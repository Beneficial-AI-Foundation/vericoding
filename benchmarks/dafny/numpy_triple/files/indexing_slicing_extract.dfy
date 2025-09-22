// <vc-preamble>
// Helper predicate to count True values in a boolean sequence
function CountTrue(condition: seq<bool>): nat
{
    if |condition| == 0 then 0
    else (if condition[0] then 1 else 0) + CountTrue(condition[1..])
}

// Helper predicate to check if result contains elements from arr where condition is True, in order
ghost predicate ValidExtract(condition: seq<bool>, arr: seq<real>, result: seq<real>)
  requires |condition| == |arr|
{
    |result| == CountTrue(condition) &&
    exists mapping: seq<nat> ::
      |mapping| == |result| &&
      (forall i :: 0 <= i < |mapping| ==> 
        0 <= mapping[i] < |condition| &&
        condition[mapping[i]]) &&
      (forall i :: 0 <= i < |result| ==> 
        result[i] == arr[mapping[i]]) &&
      (forall i, j :: 0 <= i < j < |mapping| ==> 
        mapping[i] < mapping[j])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Extract(condition: seq<bool>, arr: seq<real>) returns (result: seq<real>)
  requires |condition| == |arr|
  ensures ValidExtract(condition, arr, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
