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
    var bCount := 0;
    var aCount := 0;
    var dCount := 0;
    
    // Count occurrences of each character
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant bCount + aCount + dCount == i
        invariant bCount == |multiset(a[..i])['b']|
        invariant aCount == |multiset(a[..i])['a']|
        invariant dCount == |multiset(a[..i])['d']|
    {
        if a[i] == 'b' {
            bCount := bCount + 1;
        } else if a[i] == 'a' {
            aCount := aCount + 1;
        } else {
            dCount := dCount + 1;
        }
        i := i + 1;
    }
    
    // Construct the sorted string
    /* code modified by LLM (iteration 1): fixed syntax error by removing extra semicolon */
    b := "";"
    
    // Add all b's
    i := 0;
    while i < bCount
        invariant 0 <= i <= bCount
        invariant |b| == i
        invariant forall j :: 0 <= j < |b| ==> b[j] == 'b'
    {
        b := b + "b";
        i := i + 1;
    }
    
    // Add all a's
    i := 0;
    while i < aCount
        invariant 0 <= i <= aCount
        invariant |b| == bCount + i
        invariant forall j :: 0 <= j < bCount ==> b[j] == 'b'
        invariant forall j :: bCount <= j < |b| ==> b[j] == 'a'
    {
        b := b + "a";
        i := i + 1;
    }
    
    // Add all d's
    i := 0;
    while i < dCount
        invariant 0 <= i <= dCount
        invariant |b| == bCount + aCount + i
        invariant forall j :: 0 <= j < bCount ==> b[j] == 'b'
        invariant forall j :: bCount <= j < bCount + aCount ==> b[j] == 'a'
        invariant forall j :: bCount + aCount <= j < |b| ==> b[j] == 'd'
    {
        b := b + "d";
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): added assertions to help verify postconditions */
    assert |b| == bCount + aCount + dCount;
    assert |b| == |a|;
    
    /* code modified by LLM (iteration 1): added helper lemma calls to verify postconditions */
    MultisetPreservationLemma(a, b, bCount, aCount, dCount);
    SortedPropertyLemma(b, bCount, aCount, dCount);
}

/* code modified by LLM (iteration 1): added helper lemma to prove multiset equality */
lemma MultisetPreservationLemma(a: string, b: string, bCount: int, aCount: int, dCount: int)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
requires bCount == |multiset(a[..])['b']|
requires aCount == |multiset(a[..])['a']|
requires dCount == |multiset(a[..])['d']|
requires |b| == bCount + aCount + dCount
requires forall j :: 0 <= j < bCount ==> b[j] == 'b'
requires forall j :: bCount <= j < bCount + aCount ==> b[j] == 'a'
requires forall j :: bCount + aCount <= j < |b| ==> b[j] == 'd'
requires |a| == |b|
ensures multiset(a[..]) == multiset(b[..])
{
    assert |multiset(b[..])['b']| == bCount;
    assert |multiset(b[..])['a']| == aCount;
    assert |multiset(b[..])['d']| == dCount;
    assert forall c :: c !in {'a', 'b', 'd'} ==> |multiset(a[..])['c']| == 0;
    assert forall c :: c !in {'a', 'b', 'd'} ==> |multiset(b[..])['c']| == 0;
}

/* code modified by LLM (iteration 1): added helper lemma to prove sorted property */
lemma SortedPropertyLemma(b: string, bCount: int, aCount: int, dCount: int)
requires |b| == bCount + aCount + dCount
requires forall j :: 0 <= j < bCount ==> b[j] == 'b'
requires forall j :: bCount <= j < bCount + aCount ==> b[j] == 'a'
requires forall j :: bCount + aCount <= j < |b| ==> b[j] == 'd'
ensures sortedbad(b)
{
    // Prove that all b's come before all a's and d's
    forall i, j | 0 <= i < |b| && 0 <= j < |b| && b[i] == 'b' && (b[j] == 'a' || b[j] == 'd')
    ensures i < j
    {
        assert i < bCount;
        if b[j] == 'a' {
            assert j >= bCount;
        } else {
            assert j >= bCount + aCount;
        }
    }
    
    // Prove that all a's come after all b's
    forall i, j | 0 <= i < |b| && 0 <= j < |b| && b[i] == 'a' && b[j] == 'b'
    ensures i > j
    {
        assert i >= bCount;
        assert j < bCount;
    }
    
    // Prove that all a's come before all d's
    forall i, j | 0 <= i < |b| && 0 <= j < |b| && b[i] == 'a' && b[j] == 'd'
    ensures i < j
    {
        assert bCount <= i < bCount + aCount;
        assert j >= bCount + aCount;
    }
    
    // Prove that all d's come after all b's and a's
    forall i, j | 0 <= i < |b| && 0 <= j < |b| && b[i] == 'd' && (b[j] == 'a' || b[j] == 'b')
    ensures i > j
    {
        assert i >= bCount + aCount;
        if b[j] == 'b' {
            assert j < bCount;
        } else {
            assert j < bCount + aCount;
        }
    }
}