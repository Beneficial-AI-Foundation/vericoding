//ATOM
// verifies
// all bs are before all as which are before all ds
predicate sortedbad(s:string) 
{
  // all b's are before all a's and d's
  forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'b' && (s[j] == 'a' || s[j] == 'd') ==> i < j &&
  // all a's are after all b's
  forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'b' ==> i > j &&
  // all a's are before all d's
  forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'd' ==> i < j &&
  // all d's are after a;; b's and a's
  forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'd' && (s[j] == 'a' || s[j] == 'b') ==> i > j
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
    
    /* code modified by LLM (iteration 1): Fixed loop syntax and string operations */
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
            bs := bs + [a[i]];
        } else if a[i] == 'a' {
            as := as + [a[i]];
        } else {
            ds := ds + [a[i]];
        }
        i := i + 1;
    }
    
    b := bs + as + ds;
    
    /* code modified by LLM (iteration 1): Added lemma call to establish postconditions */
    BadSortCorrect(a, bs, as, ds, b);
}

/* code modified by LLM (iteration 1): Added helper lemma to prove correctness */
lemma BadSortCorrect(a: string, bs: string, as: string, ds: string, b: string)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
requires forall k :: 0 <= k < |bs| ==> bs[k] == 'b'
requires forall k :: 0 <= k < |as| ==> as[k] == 'a'
requires forall k :: 0 <= k < |ds| ==> ds[k] == 'd'
requires multiset(a[..]) == multiset(bs[..]) + multiset(as[..]) + multiset(ds[..])
requires b == bs + as + ds
ensures sortedbad(b)
ensures multiset(a[..]) == multiset(b[..])
ensures |a| == |b|
{
    // Length property
    assert |b| == |bs| + |as| + |ds|;
    assert |b| == |a|;
    
    // Multiset property follows from transitivity
    assert multiset(b[..]) == multiset(a[..]);
    
    /* code modified by LLM (iteration 1): Added structure assertions for string concatenation */
    // Structure of b: bs followed by as followed by ds
    assert forall k :: 0 <= k < |bs| ==> b[k] == bs[k];
    assert forall k :: |bs| <= k < |bs| + |as| ==> b[k] == as[k - |bs|];
    assert forall k :: |bs| + |as| <= k < |b| ==> b[k] == ds[k - |bs| - |as|];
    
    // Therefore character properties
    assert forall k :: 0 <= k < |bs| ==> b[k] == 'b';
    assert forall k :: |bs| <= k < |bs| + |as| ==> b[k] == 'a';
    assert forall k :: |bs| + |as| <= k < |b| ==> b[k] == 'd';
    
    /* code modified by LLM (iteration 1): Prove sortedbad conditions with explicit reasoning */
    // Prove all conditions of sortedbad
    forall i,j | 0 <= i < |b| && 0 <= j < |b| && b[i] == 'b' && (b[j] == 'a' || b[j] == 'd')
        ensures i < j
    {
        assert i < |bs|; // b[i] == 'b' implies i is in bs section
        assert j >= |bs|; // b[j] is 'a' or 'd', so j is not in bs section
    }
    
    forall i,j | 0 <= i < |b| && 0 <= j < |b| && b[i] == 'a' && b[j] == 'b'
        ensures i > j
    {
        assert i >= |bs|; // b[i] == 'a' implies i is not in bs section
        assert j < |bs|; // b[j] == 'b' implies j is in bs section
    }
    
    forall i,j | 0 <= i < |b| && 0 <= j < |b| && b[i] == 'a' && b[j] == 'd'
        ensures i < j
    {
        assert |bs| <= i < |bs| + |as|; // b[i] == 'a' implies i is in as section
        assert j >= |bs| + |as|; // b[j] == 'd' implies j is in ds section
    }
    
    forall i,j | 0 <= i < |b| && 0 <= j < |b| && b[i] == 'd' && (b[j] == 'a' || b[j] == 'b')
        ensures i > j
    {
        assert i >= |bs| + |as|; // b[i] == 'd' implies i is in ds section
        assert j < |bs| + |as|; // b[j] is 'a' or 'b', so j is not in ds section
    }
}