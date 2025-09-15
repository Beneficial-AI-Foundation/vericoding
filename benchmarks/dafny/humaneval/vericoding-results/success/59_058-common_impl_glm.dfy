// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function InSeq(x: int, s: seq<int>): bool {
    exists i :: 0 <= i < |s| && s[i] == x
}

function SeqToSet(s: seq<int>): set<int> {
    set i | 0 <= i < |s| :: s[i]
}
// </vc-helpers>

// <vc-spec>
method common(l1 : seq<int>, l2 : seq<int>) returns (c : set<int>)

    ensures forall i :: i in c ==> i in l1 && i in l2
    ensures forall i :: i in l1 && i in l2 ==> i in c
// </vc-spec>
// <vc-code>
{
    var s1 := SeqToSet(l1);
    var s2 := SeqToSet(l2);
    c := s1 * s2;  // Set intersection
}
// </vc-code>
