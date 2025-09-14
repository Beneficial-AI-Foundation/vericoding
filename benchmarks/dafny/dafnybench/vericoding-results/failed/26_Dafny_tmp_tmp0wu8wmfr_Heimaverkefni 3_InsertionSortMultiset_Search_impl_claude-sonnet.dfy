// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/G4sc3

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/nujsu

// Insertion sort með hjálp helmingunarleitar.

// <vc-helpers>
lemma SeqSplitProperty<T>(s: seq<T>, k: int)
    requires 0 <= k <= |s|
    ensures s == s[..k] + s[k..]
{
}

lemma BinarySearchInvariant(s: seq<int>, x: int, lo: int, hi: int)
    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
    requires 0 <= lo <= hi <= |s|
    requires forall i | 0 <= i < lo :: s[i] <= x
    requires forall i | hi <= i < |s| :: s[i] >= x
    ensures forall i | 0 <= i < lo :: s[i] <= x
    ensures forall i | hi <= i < |s| :: s[i] >= x
{
}

lemma SliceProperties(s: seq<int>, x: int, k: int)
    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
    requires 0 <= k <= |s|
    requires forall i | 0 <= i < k :: s[i] <= x
    requires forall i | k <= i < |s| :: s[i] >= x
    ensures forall z | z in s[..k] :: z <= x
    ensures forall z | z in s[k..] :: z >= x
{
    forall z | z in s[..k]
        ensures z <= x
    {
        assert exists i | 0 <= i < k :: s[i] == z;
    }
    
    forall z | z in s[k..]
        ensures z >= x
    {
        assert exists i | k <= i < |s| :: s[i] == z;
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
    
    SliceProperties(s, x, k);
    SeqSplitProperty(s, k);
}
// </vc-code>

