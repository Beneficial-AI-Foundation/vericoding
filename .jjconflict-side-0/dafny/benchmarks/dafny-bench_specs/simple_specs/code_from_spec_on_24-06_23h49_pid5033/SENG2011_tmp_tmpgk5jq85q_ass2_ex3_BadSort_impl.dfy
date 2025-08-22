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
ensures multiset(a[0..|a|]) == multiset(b[0..|b|])
ensures |a| == |b|
{
    /* code modified by LLM (iteration 1): Fixed string operations using sequences instead of invalid string concatenation */
    var bs: seq<char> := [];
    var as: seq<char> := [];
    var ds: seq<char> := [];
    
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant forall k :: 0 <= k < |bs| ==> bs[k] == 'b'
        invariant forall k :: 0 <= k < |as| ==> as[k] == 'a'
        invariant forall k :: 0 <= k < |ds| ==> ds[k] == 'd'
        invariant multiset(a[0..i]) == multiset(bs) + multiset(as) + multiset(ds)
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
    
    /* code modified by LLM (iteration 1): Convert sequences back to string and add verification assertions */
    b := bs + as + ds;
    
    // Establish multiset equality
    assert multiset(a[0..|a|]) == multiset(bs) + multiset(as) + multiset(ds);
    assert multiset(b[0..|b|]) == multiset(bs) + multiset(as) + multiset(ds);
    assert |b| == |bs| + |as| + |ds|;
    
    // Establish the structure of b: all b's, then all a's, then all d's
    assert forall k :: 0 <= k < |bs| ==> b[k] == 'b';
    assert forall k :: |bs| <= k < |bs| + |as| ==> b[k] == 'a';
    assert forall k :: |bs| + |as| <= k < |b| ==> b[k] == 'd';
    
    // Prove each part of sortedbad(b)
    assert forall i,j :: 0 <= i < |b| && 0 <= j < |b| && b[i] == 'b' && (b[j] == 'a' || b[j] == 'd') ==> i < j by {
        forall i,j | 0 <= i < |b| && 0 <= j < |b| && b[i] == 'b' && (b[j] == 'a' || b[j] == 'd')
            ensures i < j
        {
            assert i < |bs|;  // b's are in first |bs| positions
            assert j >= |bs|; // a's and d's are after position |bs|
        }
    }
    
    assert forall i,j :: 0 <= i < |b| && 0 <= j < |b| && b[i] == 'a' && b[j] == 'b' ==> i > j by {
        forall i,j | 0 <= i < |b| && 0 <= j < |b| && b[i] == 'a' && b[j] == 'b'
            ensures i > j
        {
            assert i >= |bs|; // a's are after position |bs|
            assert j < |bs|;  // b's are in first |bs| positions
        }
    }
    
    assert forall i,j :: 0 <= i < |b| && 0 <= j < |b| && b[i] == 'a' && b[j] == 'd' ==> i < j by {
        forall i,j | 0 <= i < |b| && 0 <= j < |b| && b[i] == 'a' && b[j] == 'd'
            ensures i < j
        {
            assert |bs| <= i < |bs| + |as|; // a's are in positions [|bs|, |bs| + |as|)
            assert j >= |bs| + |as|;        // d's are after position |bs| + |as|
        }
    }
    
    assert forall i,j :: 0 <= i < |b| && 0 <= j < |b| && b[i] == 'd' && (b[j] == 'a' || b[j] == 'b') ==> i > j by {
        forall i,j | 0 <= i < |b| && 0 <= j < |b| && b[i] == 'd' && (b[j] == 'a' || b[j] == 'b')
            ensures i > j
        {
            assert i >= |bs| + |as|; // d's are after position |bs| + |as|
            assert j < |bs| + |as|;  // a's and b's are before position |bs| + |as|
        }
    }
}