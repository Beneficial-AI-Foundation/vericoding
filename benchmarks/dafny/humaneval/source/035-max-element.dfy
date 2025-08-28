method max_element(l : seq<int>) returns (result : int)
    // pre-conditions-start
    requires |l| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures forall i : int :: i >= 0 && i < |l| ==> l[i] <= result
    ensures exists i : int :: i >= 0 && i < |l| && l[i] == result
    // post-conditions-end
{
    // impl-start
    result := l[0];
    var i : int := 1;
    while i < |l|
        // invariants-start
        invariant i >= 1 && i <= |l|
        invariant forall i1 : int :: i1 >= 0 && i1 < i ==> l[i1] <= result
        invariant exists i1 : int :: i1 >= 0 && i1 < i && l[i1] == result
        // invariants-end
    {
        if l[i] > result {
            result := l[i];
        }
        i := i + 1;
    }
    // impl-end
}
