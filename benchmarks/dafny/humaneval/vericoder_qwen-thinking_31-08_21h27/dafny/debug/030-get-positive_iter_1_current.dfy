

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method get_positive(l : seq<int>) returns (result : seq<int>)
    // post-conditions-start
    ensures forall i : int :: i >= 0 && i < |result| ==> result[i] > 0
    ensures |result| <= |l|
    ensures forall i1 :: i1 >= 0 && i1 < |l| ==> (l[i1] > 0 ==> exists i2 :: i2 >= 0 && i2 < |result| && result[i2] == l[i1])
    ensures |result| == 0 || (forall i1 : int :: i1 >= 0 && i1 < |result| ==> (exists i2 :: i2 >= 0 && i2 < |l| && l[i2] == result[i1]))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{ return [x | x in l where x > 0]; }
// </vc-code>

