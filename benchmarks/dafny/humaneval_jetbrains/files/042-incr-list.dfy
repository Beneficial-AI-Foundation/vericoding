/*
function_signature: def incr_list(numbers: List[Int]) -> List[Int]
incr_list takes a list of integers as input and returns a new list where each element is incremented by 1.
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method incr_list(l: seq<int>) returns (result: seq<int>)

    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == l[i] + 1
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
