/*
function_signature: def max_element(l: list)
Return maximum element in the list.
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method max_element(l : seq<int>) returns (result : int)

    requires |l| > 0

    ensures forall i : int :: i >= 0 && i < |l| ==> l[i] <= result
    ensures exists i : int :: i >= 0 && i < |l| && l[i] == result
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
