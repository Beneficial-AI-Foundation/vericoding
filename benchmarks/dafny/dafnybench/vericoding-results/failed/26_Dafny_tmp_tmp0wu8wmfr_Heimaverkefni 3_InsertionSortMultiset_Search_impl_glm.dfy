// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/G4sc3

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/nujsu

// Insertion sort með hjálp helmingunarleitar.

// <vc-helpers>
lemma LeftPartMaintained(s: seq<int>, x: int, low: int, high: int, mid: int)
    requires 0 <= low <= mid < high <= |s|
    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
    requires forall i | 0 <= i < low :: s[i] <= x
    requires s[mid] < x
    ensures forall i | 0 <= i < mid+1 :: s[i] <= x
{
    assert forall i | 0 <= i < low :: s[i] <= x;
    forall i | low <= i < mid+1 
        ensures s[i] <= x
    {
        assert s[i] <= s[mid]; 
        assert s[mid] < x;
    }
}

lemma RightPartMaintained(s: seq<int>, x: int, low: int, high: int, mid: int)
    requires 0 <= low <= mid < high <= |s|
    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
    requires forall i | high <= i < |s| :: s[i] >= x
    requires s[mid] >= x
    ensures forall i | mid <= i < |s| :: s[i] >= x
{
    assert forall i | high <= i < |s| :: s[i] >= x;
    forall i | mid <= i < high 
        ensures s[i] >= x
    {
        assert s[i] >= s[mid]; 
        assert s[mid] >= x;
    }
}
// </vc-helpers>

// <vc-spec>
method Search( s: seq<int>, x: int ) returns ( k: int )
    // Ekki má breyta forskilyrðum eða eftirskilyrðum fallsins
    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
    ensures 0 <= k <= |s|;
    ensures forall i | 0 <= i < k :: s[i] <= x;
    ensures forall i | k <= i < |s| :: s[i] >= x;
    ensures forall z | z in s[..k] :: z <= x;
    ensures forall z | z in s[k..] :: z >= x;
    ensures s == s[..k]+s[k..];
// </vc-spec>
// <vc-code>
{
    var low, high := 0, |s|;
    while low < high
        invariant 0 <= low <= high <= |s|
        invariant forall i | 0 <= i < low :: s[i] <= x
        invariant forall i | high <= i < |s| :: s[i] >= x
    {
        var mid := (low + high) / 2;
        if s[mid] < x {
            LeftPartMaintained(s, x, low, high, mid);
            low := mid + 1;
        } else {
            RightPartMaintained(s, x, low, high, mid);
            high := mid;
        }
    }
    return low;
}
// </vc-code>

