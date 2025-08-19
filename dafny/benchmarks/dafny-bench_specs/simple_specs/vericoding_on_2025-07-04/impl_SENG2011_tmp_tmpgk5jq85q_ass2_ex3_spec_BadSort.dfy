//ATOM
// verifies
// all bs are before all as which are before all ds
predicate sortedbad(s:string) 
{
  // all b's are before all a's and d's
  (forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'b' && (s[j] == 'a' || s[j] == 'd') ==> i < j) &&
  // all a's are after all b's
  (forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'b' ==> i > j) &&
  // all a's are before all d's
  (forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'd' ==> i < j) &&
  // all d's are after all b's and a's
  (forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'd' && (s[j] == 'a' || s[j] == 'b') ==> i > j)
}

//IMPL BadSort
method BadSort(a: string) returns (b: string)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
ensures sortedbad(b)
ensures multiset(a[..]) == multiset(b[..])
ensures |a| == |b|
{
    var bs := "";
    var as := "";
    var ds := "";
    
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant |bs| + |as| + |ds| == i
        invariant forall k :: 0 <= k < |bs| ==> bs[k] == 'b'
        invariant forall k :: 0 <= k < |as| ==> as[k] == 'a'
        invariant forall k :: 0 <= k < |ds| ==> ds[k] == 'd'
        invariant multiset(a[..i]) == multiset(bs[..]) + multiset(as[..]) + multiset(ds[..])
    {
        if a[i] == 'b' {
            bs := bs + "b";
        } else if a[i] == 'a' {
            as := as + "a";
        } else {
            ds := ds + "d";
        }
        i := i + 1;
    }
    
    b := bs + as + ds;
    
    /* code modified by LLM (iteration 1): added helper lemma call to prove sortedbad property */
    ConcatenationPreservesOrder(bs, as, ds);
}

/* code modified by LLM (iteration 1): added helper lemma to prove concatenation maintains sorted order */
lemma ConcatenationPreservesOrder(bs: string, as: string, ds: string)
requires forall k :: 0 <= k < |bs| ==> bs[k] == 'b'
requires forall k :: 0 <= k < |as| ==> as[k] == 'a'
requires forall k :: 0 <= k < |ds| ==> ds[k] == 'd'
ensures sortedbad(bs + as + ds)
{
    var s := bs + as + ds;
    
    /* code modified by LLM (iteration 1): added string concatenation length assertions */
    assert |s| == |bs| + |as| + |ds|;
    assert s[..|bs|] == bs;
    assert s[|bs|..|bs|+|as|] == as;
    assert s[|bs|+|as|..] == ds;
    
    // Prove all conditions of sortedbad
    forall i, j | 0 <= i < |s| && 0 <= j < |s| && s[i] == 'b' && (s[j] == 'a' || s[j] == 'd')
        ensures i < j
    {
        /* code modified by LLM (iteration 1): strengthened position assertions */
        assert i < |bs|; // b's are in positions 0..|bs|-1
        if s[j] == 'a' {
            assert |bs| <= j < |bs| + |as|; // a's are in positions |bs|..|bs|+|as|-1
        } else {
            assert j >= |bs| + |as|; // d's are in positions |bs|+|as|..|s|-1
        }
        assert i < |bs| <= j;
    }
    
    forall i, j | 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'b'
        ensures i > j
    {
        assert |bs| <= i < |bs| + |as| && j < |bs|;
    }
    
    forall i, j | 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'd'
        ensures i < j
    {
        assert |bs| <= i < |bs| + |as| && j >= |bs| + |as|;
    }
    
    forall i, j | 0 <= i < |s| && 0 <= j < |s| && s[i] == 'd' && (s[j] == 'a' || s[j] == 'b')
        ensures i > j
    {
        assert i >= |bs| + |as|;
        if s[j] == 'b' {
            assert j < |bs|;
        } else {
            assert j < |bs| + |as|;
        }
    }
}