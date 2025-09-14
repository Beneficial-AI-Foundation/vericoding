// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/G4sc3

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/nujsu

// Insertion sort með hjálp helmingunarleitar.

// <vc-helpers>
// No additional helpers needed for this implementation
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
    var lo := 0;
    var hi := |s|;
    
    while lo < hi
        invariant 0 <= lo <= hi <= |s|
        invariant forall i | 0 <= i < lo :: s[i] <= x
        invariant forall i | hi <= i < |s| :: s[i] >= x
    {
        var mid := (lo + hi) / 2;
        if s[mid] <= x {
            lo := mid + 1;
        } else {
            hi := mid;
        }
    }
    
    k := lo;
    
    assert s == s[..k] + s[k..];
    assert forall z | z in s[..k] :: z <= x;
    assert forall z | z in s[k..] :: z >= x;
}
// </vc-code>

