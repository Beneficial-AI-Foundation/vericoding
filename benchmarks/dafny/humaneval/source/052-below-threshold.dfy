method below_threshold(l : seq<int>, t : int) returns (b : bool)
    // post-conditions-start
    ensures b == (forall i : int :: i >= 0 && i < |l| ==> l[i] < t)
    // post-conditions-end
{
    // impl-start
    b := true;
    var i : int := 0;
    while (i < |l|)
        // invariants-start
        invariant 0 <= i && i <= |l|
        invariant b == (forall i1 : int :: i1 >= 0 && i1 < i ==> l[i1] < t)
        // invariants-end
    {
        if (l[i] >= t)
        {
            b := false;
        }
        i := i + 1;
    }
    // impl-end
}
