

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method below_threshold(l : seq<int>, t : int) returns (b : bool)
    // post-conditions-start
    ensures b == (forall i : int :: i >= 0 && i < |l| ==> l[i] < t)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  b := (forall i:int :: i >= 0 && i < |l| ==> l[i] < t);
}
// </vc-code>

