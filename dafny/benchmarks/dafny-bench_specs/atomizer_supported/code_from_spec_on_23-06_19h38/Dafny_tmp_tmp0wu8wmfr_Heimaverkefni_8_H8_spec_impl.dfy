// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/GW7a

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://www.rise4fun.com/Dafny/JPGct

// Klárið að forrita föllin tvö.

//IMPL Partition
method Partition( m: multiset<int> )
        returns( pre: multiset<int>, p: int, post: multiset<int> )
    requires |m| > 0;
    ensures p in m;
    ensures m == pre+multiset{p}+post;
    ensures forall z | z in pre :: z <= p;
    ensures forall z | z in post :: z >= p;
{
    p :| p in m;
    var m' := m - multiset{p};
    pre := multiset{};
    post := multiset{};
    
    while m' != multiset{}
        invariant m == pre + multiset{p} + post + m';
        invariant forall z | z in pre :: z <= p;
        invariant forall z | z in post :: z >= p;
        decreases |m'|;
    {
        var temp :| temp in m';
        m' := m' - multiset{temp};
        if temp <= p
        {
            pre := pre + multiset{temp};
        }
        else
        {
            post := post + multiset{temp};
        }
    }
}

//IMPL QuickSelect
method QuickSelect( m: multiset<int>, k: int )
        returns( pre: multiset<int>, kth: int, post: multiset<int> )
    requires 0 <= k < |m|;
    ensures kth in m;
    ensures m == pre+multiset{kth}+post;
    ensures |pre| == k;
    ensures forall z | z in pre :: z <= kth;
    ensures forall z | z in post :: z >= kth;
    decreases |m|;
{
    var pre_part, p, post_part := Partition(m);
    
    if |pre_part| == k
    {
        pre := pre_part;
        kth := p;
        post := post_part;
    }
    else if k < |pre_part|
    {
        var pre_rec, kth_rec, post_rec := QuickSelect(pre_part, k);
        pre := pre_rec;
        kth := kth_rec;
        post := post_rec + multiset{p} + post_part;
    }
    else // k > |pre_part|
    {
        var remaining := post_part;
        var k_adjusted := k - |pre_part| - 1;
        var pre_rec, kth_rec, post_rec := QuickSelect(remaining, k_adjusted);
        pre := pre_part + multiset{p} + pre_rec;
        kth := kth_rec;
        post := post_rec;
    }
}