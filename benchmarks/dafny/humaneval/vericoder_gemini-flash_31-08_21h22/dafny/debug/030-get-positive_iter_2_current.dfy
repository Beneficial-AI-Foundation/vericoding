

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
{
    var result_seq: seq<int> := [];
    var i := 0;
    while i < |l|
        invariant 0 <= i <= |l|
        invariant forall j : int :: 0 <= j < |result_seq| ==> result_seq[j] > 0
        invariant |result_seq| <= i
        invariant forall k :: 0 <= k < |result_seq| ==> (exists m :: 0 <= m < i && l[m] == result_seq[k])
        invariant forall k1 :: 0 <= k1 < i ==> (l[k1] > 0 ==> exists k2 :: 0 <= k2 < |result_seq| && result_seq[k2] == l[k1])
        invariant forall k1 : int :: 0 <= k1 < |result_seq| ==> (exists k2 : int :: 0 <= k2 < |l| && l[k2] == result_seq[k1])
    {
        if l[i] > 0 {
            result_seq := result_seq + [l[i]];
        }
        i := i + 1;
    }
    return result_seq;
}
// </vc-code>

