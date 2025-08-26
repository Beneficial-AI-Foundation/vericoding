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
    // Setjið viðeigandi stofn fallsins hér.
    var p := 0;
    var q := |s|;

    if p == q
    {
        return p;
    }
    while p != q 
        decreases q-p;
        invariant 0 <= p <= q <= |s|;
        invariant forall r | 0 <= r < p :: s[r] <= x;
        invariant forall r | q <= r < |s| :: s[r] >= x;

    {
        var m := p + (q-p)/2;
        if s[m] <= x
        {
            p := m+1;
        }
        else
        {
            q := m;
        }
    }

    SliceEqualityLemma(s, p);
    return p;
}

// <vc-helpers>
lemma MultisetInsertionLemma<T>(s: seq<T>, x: T, k: int)
    requires 0 <= k <= |s|
    ensures multiset(s[..k] + [x] + s[k..]) == multiset(s) + multiset{x}
{
    assert s[..k] + [x] + s[k..] == s[..k] + ([x] + s[k..]);
    assert multiset(s[..k] + ([x] + s[k..])) == multiset(s[..k]) + multiset([x] + s[k..]);
    assert multiset([x] + s[k..]) == multiset{x} + multiset(s[k..]);
    SliceEqualityLemma(s, k);
    assert multiset(s[..k]) + multiset(s[k..]) == multiset(s);
}

lemma MultisetSliceLemma<T>(s: seq<T>, i: int)
    requires 0 <= i < |s|
    ensures multiset(s[i..]) == multiset{s[i]} + multiset(s[i+1..])
{
    assert s[i..] == [s[i]] + s[i+1..];
    assert multiset(s[i..]) == multiset([s[i]] + s[i+1..]);
    assert multiset([s[i]] + s[i+1..]) == multiset([s[i]]) + multiset(s[i+1..]);
    assert multiset([s[i]]) == multiset{s[i]};
}

lemma SliceEqualityLemma<T>(s: seq<T>, k: int)
    requires 0 <= k <= |s|
    ensures s == s[..k] + s[k..]
    ensures multiset(s[..k]) + multiset(s[k..]) == multiset(s)
{
    assert s == s[..k] + s[k..];
    assert multiset(s) == multiset(s[..k] + s[k..]);
    assert multiset(s[..k] + s[k..]) == multiset(s[..k]) + multiset(s[k..]);
}
// </vc-helpers>

method Sort( m: multiset<int> ) returns ( r: seq<int> )
    ensures multiset(r) == m;
    ensures forall p,q | 0 <= p < q < |r| :: r[p] <= r[q];
// </vc-spec>
// <vc-code>
{
    var elements := [];
    var remaining := m;
    
    // Convert multiset to sequence
    while remaining != multiset{}
        decreases |remaining|;
        invariant multiset(elements) + remaining == m;
    {
        var x :| x in remaining;
        elements := elements + [x];
        remaining := remaining - multiset{x};
    }
    
    // Now sort using insertion sort with binary search
    r := [];
    var i := 0;
    while i < |elements|
        decreases |elements| - i;
        invariant 0 <= i <= |elements|;
        invariant multiset(r) + multiset(elements[i..]) == m;
        invariant forall p,q | 0 <= p < q < |r| :: r[p] <= r[q];
    {
        var x := elements[i];
        var k := Search(r, x);
        
        // Prove that the insertion maintains the multiset invariant
        MultisetSliceLemma(elements, i);
        assert multiset(elements[i..]) == multiset{x} + multiset(elements[i+1..]);
        MultisetInsertionLemma(r, x, k);
        
        r := r[..k] + [x] + r[k..];
        i := i + 1;
    }
}
// </vc-code>