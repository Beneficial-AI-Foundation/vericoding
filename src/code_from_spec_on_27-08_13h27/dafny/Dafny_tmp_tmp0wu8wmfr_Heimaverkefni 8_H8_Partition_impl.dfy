// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/GW7a

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://www.rise4fun.com/Dafny/JPGct

// Klárið að forrita föllin tvö.

// <vc-helpers>
// Helper lemma to ensure properties of multisets and partitions
lemma MultisetProperties(m: multiset<int>, pre: multiset<int>, p: int, post: multiset<int>)
    ensures m == pre + multiset{p} + post ==> p in m
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Partition( m: multiset<int> )
        returns( pre: multiset<int>, p: int, post: multiset<int> )
    requires |m| > 0;
    ensures p in m;
    ensures m == pre+multiset{p}+post;
     ensures forall z | z in pre :: z <= p;
     ensures forall z | z in post :: z >= p;
// </vc-spec>
// </vc-spec>

// <vc-code>
method PartitionImpl(m: multiset<int>)
        returns (pre: multiset<int>, p: int, post: multiset<int>)
    requires |m| > 0
    ensures p in m
    ensures m == pre + multiset{p} + post
    ensures forall z | z in pre :: z <= p
    ensures forall z | z in post :: z >= p
{
    // Choose an arbitrary element from the multiset as the pivot
    var s :| s in m;
    p := s;
    
    // Initialize pre and post as empty multisets
    pre := multiset{};
    post := multiset{};
    
    // Convert multiset to a sequence of elements by repeating each element according to its multiplicity
    var elements: seq<int> := [];
    var keys := m;
    while keys != multiset{}
        decreases |keys|
    {
        var x :| x in keys;
        var count := keys[x];
        var i := 0;
        while i < count
            decreases count - i
        {
            elements := elements + [x];
            i := i + 1;
        }
        keys := keys - multiset{ x } * count;
    }
    
    // Iterate through the sequence of elements
    var i := 0;
    while i < |elements|
        invariant 0 <= i <= |elements|
        invariant pre + post + multiset{p} <= m
        invariant forall z | z in pre :: z <= p
        invariant forall z | z in post :: z >= p
    {
        var x := elements[i];
        if x < p
        {
            pre := pre + multiset{x};
        }
        else if x > p
        {
            post := post + multiset{x};
        }
        i := i + 1;
    }
}
// </vc-code>
