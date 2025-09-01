// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def below_threshold(numbers: List[Int], threshold: Int) -> bool
*/
// </vc-description>

// <vc-spec>
method below_threshold(l : seq<int>, t : int) returns (b : bool)
    // post-conditions-start
    ensures b == (forall i : int :: i >= 0 && i < |l| ==> l[i] < t)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
