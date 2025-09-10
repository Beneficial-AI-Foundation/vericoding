method incr_list(l: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == l[i] + 1
    // post-conditions-end
{
    // impl-start
    result := [];
    var i := 0;
    while i < |l|
        // invariants-start
        invariant 0 <= i <= |l|
        invariant |result| == i
        invariant forall i1 :: 0 <= i1 < i ==> result[i1] == l[i1] + 1
        // invariants-end
    {
        result := result + [l[i] + 1];
        i := i + 1;
    }
    // impl-end
}
