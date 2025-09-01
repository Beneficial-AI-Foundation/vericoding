

// <vc-helpers>
lemma Lemma_forall_below_threshold(s: seq<int>, t: int)
    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] < t <==> 
        (forall j : int :: 0 <= j < |s| ==> s[j] < t)
{
    calc {
        forall i : int :: i >= 0 && i < |s| ==> s[i] < t;
    }
    assert forall i : int :: i >= 0 && i < |s| ==> i >= 0;
    assert forall i : int :: i >= 0 && i < |s| ==> i < |s|;
    calc {
        forall i : int :: i >= 0 && i < |s| ==> s[i] < t;
        <== 
        forall i : int :: 0 <= i < |s| ==> s[i] < t;
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method below_threshold(l : seq<int>, t : int) returns (b : bool)
    // post-conditions-start
    ensures b == (forall i : int :: i >= 0 && i < |l| ==> l[i] < t)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    return forall i : int :: 0 <= i < |l| ==> l[i] < t;
}
// </vc-code>

