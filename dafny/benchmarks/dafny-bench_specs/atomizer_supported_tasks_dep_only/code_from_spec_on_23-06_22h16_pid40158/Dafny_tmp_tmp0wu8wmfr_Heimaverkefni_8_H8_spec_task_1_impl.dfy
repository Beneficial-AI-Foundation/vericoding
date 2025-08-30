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
    ensures m == pre + multiset{p} + post;
    ensures forall z | z in pre :: z <= p;
    ensures forall z | z in post :: z >= p;
{
    p :| p in m;
    var m' := m - multiset{p};
    pre := multiset{};
    post := multiset{};
    
    while m' != multiset{}
        invariant m' + pre + post + multiset{p} == m;
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
    requires |m| > 0;
    requires 0 <= k < |m|;
    ensures kth in m;
    ensures m == pre + multiset{kth} + post;
    ensures |pre| == k;
    ensures forall z | z in pre :: z <= kth;
    ensures forall z | z in post :: z >= kth;
    decreases |m|;
{
    var initial_pre, pivot, initial_post := Partition(m);
    
    if |initial_pre| == k
    {
        pre := initial_pre;
        kth := pivot;
        post := initial_post;
        return;
    }
    else if k < |initial_pre|
    {
        /* code modified by LLM (iteration 1): Fixed recursive call to search in the correct partition and properly construct result */
        var rec_pre, rec_kth, rec_post := QuickSelect(initial_pre, k);
        pre := rec_pre;
        kth := rec_kth;
        post := rec_post + multiset{pivot} + initial_post;
    }
    else // k > |initial_pre|
    {
        /* code modified by LLM (iteration 1): Fixed recursive call with correct k adjustment and proper result construction */
        var rec_pre, rec_kth, rec_post := QuickSelect(initial_post, k - |initial_pre| - 1);
        pre := initial_pre + multiset{pivot} + rec_pre;
        kth := rec_kth;
        post := rec_post;
    }
}