// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/G4sc3

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/nujsu

// Insertion sort með hjálp helmingunarleitar.

// IMPL 
// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/G4sc3

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/nujsu

// Insertion sort með hjálp helmingunarleitar.

method Search( s: seq<int>, x: int ) returns ( k: int )
    // Ekki má breyta forskilyrðum eða eftirskilyrðum fallsins
    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
    ensures 0 <= k <= |s|;
    ensures forall i | 0 <= i < k :: s[i] <= x;
    ensures forall i | k <= i < |s| :: s[i] >= x;
    ensures forall z | z in s[..k] :: z <= x;
    ensures forall z | z in s[k..] :: z >= x;
    ensures s == s[..k]+s[k..];
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
}


// IMPL 

method Sort( m: multiset<int> ) returns ( r: seq<int> )
    ensures multiset(r) == m;
    ensures forall p,q | 0 <= p < q < |r| :: r[p] <= r[q];
{
    r := [];
    var remaining := m;
    
    while remaining != multiset{}
        invariant multiset(r) + remaining == m
        invariant forall p,q | 0 <= p < q < |r| :: r[p] <= r[q]
        decreases |remaining|
    {
        var x :| x in remaining;
        remaining := remaining - multiset{x};
        
        var pos := Search(r, x);
        r := r[..pos] + [x] + r[pos..];
    }
}